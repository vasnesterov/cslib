/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Rooted spanning trees given by parent pointers

A rooted spanning tree of a graph `G` is described by a root, a parent function and a depth
function: every non-root vertex `v` is adjacent in `G` to `parent v`, and the depth drops by one
when passing to the parent. The tree edges are `s(v, parent v)` for `v ≠ root`. Since the depth
strictly decreases along parents, following parents from any vertex reaches the root after
exactly `depth v` steps, so the tree edges form a spanning tree of `G` and `depth v` is the
distance from `v` to the root in that tree.

This representation is convenient for "process the tree edges level by level" arguments
(low-congestion shortcuts, BFS trees in distributed algorithms).

## Main definitions

* `SimpleGraph.RootedTree G`: a rooted spanning tree of `G`.
* `RootedTree.edge v = s(v, parent v)`, `RootedTree.edgeSet`: the tree edges.
* `RootedTree.DepthLE T D`: all depths are at most `D`.
* `RootedTree.climb T H x`: climb from `x` towards the root as long as the edge to the parent
  lies in the edge set `H`.

## Main results

* `RootedTree.depth_iterate`, `RootedTree.iterate_depth`: `parent^[n]` lowers the depth by `n`
  and reaches the root after `depth v` steps.
* `RootedTree.edge_injective`: a tree edge determines its lower endpoint.
* `RootedTree.reachable_climb`: `x` and `climb H x` are connected by edges of `H`.

BFS trees (existence of a rooted spanning tree of depth `≤ D` in a graph of diameter `≤ D`) are in
``Cslib.Foundations.Combinatorics.SimpleGraph.BFSTree``.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- A rooted spanning tree of `G`, given by parent pointers and depths. The tree edges are
`s(v, parent v)` for `v ≠ root`. -/
structure RootedTree (G : SimpleGraph V) where
  /-- The root. -/
  root : V
  /-- The parent of a vertex (`parent root = root`). -/
  parent : V → V
  /-- The depth of a vertex, i.e. its distance to the root in the tree. -/
  depth : V → ℕ
  parent_root : parent root = root
  depth_root : depth root = 0
  depth_parent : ∀ v, v ≠ root → depth (parent v) + 1 = depth v
  adj_parent : ∀ v, v ≠ root → G.Adj v (parent v)

namespace RootedTree

variable {G : SimpleGraph V} (T : G.RootedTree)

/-- All vertices have depth at most `D`. -/
def DepthLE (D : ℕ) : Prop := ∀ v, T.depth v ≤ D

/-- The tree edge from `v` to its parent. -/
def edge (v : V) : Sym2 V := s(v, T.parent v)

/-- The set of tree edges. -/
def edgeSet : Set (Sym2 V) := {e | ∃ v, v ≠ T.root ∧ e = T.edge v}

/-- A set of edges is `T`-restricted if it consists of tree edges. -/
def Restricts (H : Finset (Sym2 V)) : Prop := ∀ e ∈ H, e ∈ T.edgeSet

variable {T}

theorem depth_pos {v : V} (hv : v ≠ T.root) : 0 < T.depth v := by
  have := T.depth_parent v hv; omega

theorem depth_eq_zero_iff {v : V} : T.depth v = 0 ↔ v = T.root := by
  constructor
  · intro h; by_contra hv; have := depth_pos hv; omega
  · rintro rfl; exact T.depth_root

theorem depth_parent_lt {v : V} (hv : v ≠ T.root) : T.depth (T.parent v) < T.depth v := by
  have := T.depth_parent v hv; omega

theorem parent_ne_self {v : V} (hv : v ≠ T.root) : T.parent v ≠ v := by
  intro h; have := depth_parent_lt hv; rw [h] at this; omega

theorem iterate_root (n : ℕ) : T.parent^[n] T.root = T.root :=
  Function.iterate_fixed T.parent_root n

/-- `parent^[n]` lowers the depth by exactly `n` (truncated at the root). -/
theorem depth_iterate (v : V) (n : ℕ) : T.depth (T.parent^[n] v) = T.depth v - n := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    by_cases hv : v = T.root
    · subst hv; rw [T.parent_root, iterate_root, T.depth_root]; simp
    · rw [ih, ← T.depth_parent v hv]; omega

theorem iterate_depth (v : V) : T.parent^[T.depth v] v = T.root := by
  rw [← depth_eq_zero_iff, depth_iterate]; simp

theorem iterate_eq_root_of_le {v : V} {n : ℕ} (h : T.depth v ≤ n) : T.parent^[n] v = T.root := by
  rw [← depth_eq_zero_iff, depth_iterate]; omega

/-- If `parent^[n] w = v` with `v` not the root, then `n` is the depth difference. -/
theorem depth_of_iterate_eq {v w : V} {n : ℕ} (h : T.parent^[n] w = v) (hv : v ≠ T.root) :
    T.depth v + n = T.depth w := by
  have h1 := depth_iterate (T := T) w n
  rw [h] at h1
  have : n < T.depth w ∨ T.depth w ≤ n := lt_or_ge _ _
  rcases this with h2 | h2
  · omega
  · exact absurd (by rw [← h]; exact iterate_eq_root_of_le h2) hv

/-- The vertices strictly below `parent^[n] w` on the path from `w` are non-root. -/
theorem iterate_ne_root_of_lt {v w : V} {n i : ℕ} (h : T.parent^[n] w = v) (hv : v ≠ T.root)
    (hi : i < n) : T.parent^[i] w ≠ T.root := by
  intro hr
  apply hv; rw [← h]
  have : n = (n - i) + i := by omega
  rw [this, Function.iterate_add_apply, hr, iterate_root]

theorem depth_iterate_lt {v w : V} {n i : ℕ} (h : T.parent^[n] w = v) (hv : v ≠ T.root)
    (hi : i < n) : T.depth v < T.depth (T.parent^[i] w) := by
  have := depth_of_iterate_eq h hv
  rw [depth_iterate]; omega

theorem adj_edge {v : V} (hv : v ≠ T.root) : G.Adj v (T.parent v) := T.adj_parent v hv

theorem edge_mem_edgeSet {v : V} (hv : v ≠ T.root) : T.edge v ∈ T.edgeSet := ⟨v, hv, rfl⟩

theorem edge_mem_graph_edgeSet {e : Sym2 V} (he : e ∈ T.edgeSet) : e ∈ G.edgeSet := by
  obtain ⟨v, hv, rfl⟩ := he; exact T.adj_parent v hv

/-- A tree edge determines its lower endpoint. -/
theorem edge_injective {u v : V} (hu : u ≠ T.root) (hv : v ≠ T.root) (h : T.edge u = T.edge v) :
    u = v := by
  unfold edge at h
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · have a := depth_parent_lt hu; have b := depth_parent_lt hv
    have c1 : T.depth u = T.depth (T.parent v) := congrArg T.depth h1
    have c2 : T.depth (T.parent u) = T.depth v := congrArg T.depth h2
    omega

/-! ### Climbing -/

variable [DecidableEq V]

set_option linter.unusedVariables false in
/-- Climb from `x` towards the root as long as the edge to the parent belongs to `H`. -/
def climb (T : G.RootedTree) (H : Finset (Sym2 V)) (x : V) : V :=
  if h : x ≠ T.root ∧ T.edge x ∈ H then climb T H (T.parent x) else x
termination_by T.depth x
decreasing_by exact depth_parent_lt h.1

theorem climb_eq (H : Finset (Sym2 V)) (x : V) :
    T.climb H x = if x ≠ T.root ∧ T.edge x ∈ H then T.climb H (T.parent x) else x := by
  rw [climb]; split_ifs <;> rfl

theorem climb_of_mem {H : Finset (Sym2 V)} {x : V} (hx : x ≠ T.root) (h : T.edge x ∈ H) :
    T.climb H x = T.climb H (T.parent x) := by
  rw [climb_eq]; exact ite_eq_left ⟨hx, h⟩

theorem climb_of_not_mem {H : Finset (Sym2 V)} {x : V} (h : ¬ (x ≠ T.root ∧ T.edge x ∈ H)) :
    T.climb H x = x := by
  rw [climb_eq]; exact ite_eq_right h

/-- The end of a climb is a top: the root, or its parent edge is not in `H`. -/
theorem climb_top (H : Finset (Sym2 V)) (x : V) :
    T.climb H x = T.root ∨ T.edge (T.climb H x) ∉ H := by
  induction hd : T.depth x using Nat.strong_induction_on generalizing x with
  | _ d ih =>
    by_cases h : x ≠ T.root ∧ T.edge x ∈ H
    · rw [climb_of_mem h.1 h.2]
      exact ih _ (hd ▸ depth_parent_lt h.1) _ rfl
    · rw [climb_of_not_mem h]
      by_cases hx : x = T.root
      · exact Or.inl hx
      · exact Or.inr fun h' => h ⟨hx, h'⟩

/-- Any property preserved by climbing one `H`-edge holds at the end of the climb. -/
theorem climb_induction (H : Finset (Sym2 V)) (p : V → Prop)
    (step : ∀ x, x ≠ T.root → T.edge x ∈ H → p x → p (T.parent x)) (x : V) (hx : p x) :
    p (T.climb H x) := by
  induction hd : T.depth x using Nat.strong_induction_on generalizing x with
  | _ d ih =>
    by_cases h : x ≠ T.root ∧ T.edge x ∈ H
    · rw [climb_of_mem h.1 h.2]
      exact ih _ (hd ▸ depth_parent_lt h.1) _ (step x h.1 h.2 hx) rfl
    · rwa [climb_of_not_mem h]

/-- `x` is connected to `climb H x` by edges of `H`. -/
theorem reachable_climb (H : Finset (Sym2 V)) (x : V) :
    (fromEdgeSet (H : Set (Sym2 V))).Reachable x (T.climb H x) :=
  climb_induction H (fun y => (fromEdgeSet (H : Set (Sym2 V))).Reachable x y)
    (fun y hy he hr => hr.trans (Adj.reachable (by
      rw [fromEdgeSet_adj]; exact ⟨he, (parent_ne_self hy).symm⟩))) x Reachable.rfl

/-- The climb from `x` reaches it in a number of steps: `climb H x = parent^[n] x` with all
intermediate edges in `H`. -/
theorem climb_eq_iterate (H : Finset (Sym2 V)) (x : V) :
    ∃ n, T.climb H x = T.parent^[n] x ∧ ∀ i < n, T.parent^[i] x ≠ T.root ∧
      T.edge (T.parent^[i] x) ∈ H := by
  induction hd : T.depth x using Nat.strong_induction_on generalizing x with
  | _ d ih =>
    by_cases h : x ≠ T.root ∧ T.edge x ∈ H
    · obtain ⟨n, hn, hi⟩ := ih _ (hd ▸ depth_parent_lt h.1) (T.parent x) rfl
      refine ⟨n + 1, by rw [climb_of_mem h.1 h.2, hn, Function.iterate_succ_apply], ?_⟩
      intro i hi'
      rcases i with _ | i
      · exact h
      · rw [Function.iterate_succ_apply]; exact hi i (by omega)
    · exact ⟨0, by rw [climb_of_not_mem h]; rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩

end RootedTree

end SimpleGraph
