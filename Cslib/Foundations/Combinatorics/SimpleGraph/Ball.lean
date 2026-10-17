/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# Closed balls, closed neighbourhoods and dominating sets

Mathlib has the *open* ball `G.ball c r = {v | G.edist v c < r}`. Distributed algorithms are
usually phrased with *closed* balls ("all nodes within distance `r`"), closed neighbourhoods
`N⁺(v) = {v} ∪ N(v)` and dominating sets; this file provides them together with the `edist`
arithmetic used to reason about balls of radius `r : ℕ`.

## Main definitions

* `SimpleGraph.closedBall G c r = {v | G.edist v c ≤ r}` (radius `r : ℕ∞`, same argument order as
  Mathlib's `SimpleGraph.ball`).
* `SimpleGraph.closedNeighborSet G v = insert v (G.neighborSet v)` and its `Finset` version
  `SimpleGraph.closedNeighborFinset`.
* `SimpleGraph.IsDominatingSet G D`: every vertex is in `D` or adjacent to a vertex of `D`.

## Main results

* `edist_le_add_one_of_adj`, `exists_adj_of_edist_eq_succ` (the penultimate vertex of a shortest
  walk), `edist_eq_natCast_iff` (finite `edist` is `dist` of a reachable pair).
* `mem_closedBall_succ_iff`: the ball recursion `B(c, t+1) = B(c, t) ∪ ⋃_{w ~ c} B(w, t)`.
* `closedBall_one`, `ball_add_one`; `isDominatingSet_iff_forall_exists_mem`.
* `Walk.le_add_length_of_lipschitz`, `le_add_edist_of_lipschitz`,
  `Reachable.le_add_dist_of_lipschitz`, `le_add_of_edist_le_of_lipschitz`: a potential `f : V → ℕ`
  growing by at most one along each edge gives lower bounds on distances, `f b ≤ f a + d(a, b)`.
* `Walk.apply_eq_of_forall_adj`, `Reachable.apply_eq_of_forall_adj`: a function constant along
  edges is constant along walks.
* `closedBall_prod_subset_closedBall_boxProd`, `fst_mem_closedBall_of_mem_boxProd`,
  `snd_mem_closedBall_of_mem_boxProd`, `closedBall_boxProd_eq_univ`: closed balls of a box product
  `G₁ □ G₂` versus products of closed balls of the factors (via Mathlib's `edist_boxProd`).
* `closedBall_eq_univ_of_preconnected`: in a preconnected graph on `n` vertices the closed ball of
  radius `n - 1` is everything.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G G' : SimpleGraph V}

/-! ### `edist` arithmetic -/

section Edist

variable {u v w x : V}

/-- Moving to a neighbour increases the distance from `u` by at most one. -/
lemma edist_le_add_one_of_adj (h : G.Adj x w) : G.edist u w ≤ G.edist u x + 1 :=
  G.edist_triangle.trans (by rw [edist_eq_one_iff_adj.2 h])

/-- A distance bounded by a natural number is finite. -/
lemma edist_ne_top_of_le_natCast {n : ℕ} (h : G.edist u v ≤ n) : G.edist u v ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.natCast_ne_top n) h

/-- Vertices at distance at most `n` are connected. -/
lemma reachable_of_edist_le_natCast {n : ℕ} (h : G.edist u v ≤ n) : G.Reachable u v :=
  reachable_of_edist_ne_top (edist_ne_top_of_le_natCast h)

/-- A distance bounded by a natural number is the cast of `dist`. -/
lemma edist_eq_natCast_dist_of_le {n : ℕ} (h : G.edist u v ≤ n) : G.edist u v = G.dist u v :=
  (reachable_of_edist_le_natCast h).coe_dist_eq_edist.symm

/-- A bound `edist ≤ n` gives the bound `dist ≤ n`. -/
lemma dist_le_of_edist_le_natCast {n : ℕ} (h : G.edist u v ≤ n) : G.dist u v ≤ n := by
  have := edist_eq_natCast_dist_of_le h
  rw [this] at h; exact_mod_cast h

/-- For connected vertices, a bound `dist ≤ n` gives the bound `edist ≤ n`. -/
lemma Reachable.edist_le_natCast {n : ℕ} (hr : G.Reachable u v) (h : G.dist u v ≤ n) :
    G.edist u v ≤ n := by
  rw [← hr.coe_dist_eq_edist]; exact_mod_cast h

/-- A finite extended distance is the distance of a reachable pair. -/
lemma edist_eq_natCast_iff {n : ℕ} : G.edist u v = n ↔ G.Reachable u v ∧ G.dist u v = n := by
  constructor
  · intro h
    have hr : G.Reachable u v := reachable_of_edist_ne_top (by rw [h]; exact ENat.natCast_ne_top _)
    refine ⟨hr, ?_⟩
    have := hr.coe_dist_eq_edist
    rw [h] at this
    exact_mod_cast this
  · rintro ⟨hr, rfl⟩
    exact hr.coe_dist_eq_edist.symm

/-- Triangle inequality with natural-number bounds. -/
lemma edist_le_natCast_add {m n : ℕ} (h₁ : G.edist u v ≤ m) (h₂ : G.edist v w ≤ n) :
    G.edist u w ≤ (m + n : ℕ) := by
  calc G.edist u w ≤ G.edist u v + G.edist v w := G.edist_triangle
    _ ≤ m + n := add_le_add h₁ h₂
    _ = ((m + n : ℕ) : ℕ∞) := by push_cast; rfl

/-- The penultimate vertex of a shortest walk: if `d(u, x) = n + 1`, then `x` has a neighbour at
distance `n` from `u`. -/
lemma exists_adj_of_edist_eq_succ {n : ℕ} (h : G.edist u x = (n + 1 : ℕ)) :
    ∃ y, G.edist u y = n ∧ G.Adj y x := by
  obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_coe h
  cases hq : p.reverse with
  | nil => have := congrArg Walk.length hq; rw [Walk.length_reverse, hp] at this; simp at this
  | cons hxy q =>
    rename_i y
    have hlen : q.length = n := by
      have := congrArg Walk.length hq; simp at this; omega
    refine ⟨y, le_antisymm ?_ ?_, hxy.symm⟩
    · rw [edist_comm]; exact (edist_le q).trans (by rw [hlen])
    · have h1 := edist_le_add_one_of_adj (u := u) hxy.symm
      rw [h] at h1
      have : ((n : ℕ∞) + 1) ≤ G.edist u y + 1 := by simpa using h1
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 this

end Edist

/-! ### Closed balls -/

section ClosedBall

variable (G) in
/-- The closed ball of radius `r` centered at `c`: the vertices at extended distance at most `r`
from `c`. -/
def closedBall (c : V) (r : ℕ∞) : Set V := {v | G.edist v c ≤ r}

variable {c v : V} {r r₁ r₂ : ℕ∞}

/-- Membership in a closed ball, with the distance measured to the center. -/
@[simp] lemma mem_closedBall : v ∈ G.closedBall c r ↔ G.edist v c ≤ r := .rfl

/-- Membership in a closed ball, with the distance measured from the center. -/
lemma mem_closedBall' : v ∈ G.closedBall c r ↔ G.edist c v ≤ r := by
  rw [mem_closedBall, edist_comm]

/-- `v` is in the ball of radius `r` around `c` iff `c` is in the ball around `v`. -/
lemma mem_closedBall_comm : v ∈ G.closedBall c r ↔ c ∈ G.closedBall v r := by
  simp [edist_comm]

/-- The center lies in its closed ball. -/
lemma mem_closedBall_self : c ∈ G.closedBall c r := by simp

/-- Closed balls grow with the radius. -/
@[gcongr] lemma closedBall_mono (h : r₁ ≤ r₂) : G.closedBall c r₁ ⊆ G.closedBall c r₂ :=
  fun _ hv => le_trans hv h

/-- Closed balls grow with the graph. -/
lemma closedBall_mono_graph (h : G ≤ G') : G.closedBall c r ⊆ G'.closedBall c r :=
  fun _ hv => (edist_anti h).trans hv

/-- The closed ball of radius `0` is the center. -/
@[simp] lemma closedBall_zero : G.closedBall c 0 = {c} := by
  ext v; simp

/-- The open ball is contained in the closed ball of the same radius. -/
lemma ball_subset_closedBall : G.ball c r ⊆ G.closedBall c r := fun _ hv => (mem_ball.1 hv).le

/-- For finite `r`, the open ball of radius `r + 1` is the closed ball of radius `r`. -/
lemma ball_add_one (hr : r ≠ ⊤) : G.ball c (r + 1) = G.closedBall c r := by
  ext v; simp [ENat.lt_add_one_iff hr]

/-- The closed ball of radius `⊤` is everything. -/
@[simp] lemma closedBall_top : G.closedBall c ⊤ = Set.univ := by
  ext v; simp

/-- The vertices of a closed ball of finite radius are connected to the center. -/
lemma reachable_of_mem_closedBall {n : ℕ} (hv : v ∈ G.closedBall c n) : G.Reachable v c :=
  reachable_of_edist_le_natCast hv

/-- If `x ∈ B(c, a)` then `B(x, b) ⊆ B(c, a + b)`. -/
lemma closedBall_subset_closedBall_of_mem {x : V} {a b : ℕ∞} (hx : x ∈ G.closedBall c a) :
    G.closedBall x b ⊆ G.closedBall c (a + b) := fun v hv => by
  rw [mem_closedBall] at hx hv ⊢
  calc G.edist v c ≤ G.edist v x + G.edist x c := G.edist_triangle
    _ ≤ b + a := add_le_add hv hx
    _ = a + b := add_comm _ _

/-- The ball recursion: `B(c, t + 1) = B(c, t) ∪ ⋃_{w ~ c} B(w, t)`. -/
lemma mem_closedBall_succ_iff {t : ℕ} :
    v ∈ G.closedBall c (t + 1 : ℕ) ↔
      v ∈ G.closedBall c t ∨ ∃ w, G.Adj c w ∧ v ∈ G.closedBall w t := by
  simp only [mem_closedBall']
  constructor
  · intro h
    by_cases ht : G.edist c v ≤ t
    · exact Or.inl ht
    · right
      obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (edist_ne_top_of_le_natCast h)
      rw [← hj] at h ht
      have hj' : j = t + 1 := by
        have h1 : j ≤ t + 1 := by exact_mod_cast h
        have h2 : ¬ j ≤ t := by exact_mod_cast ht
        omega
      subst hj'
      rw [edist_comm] at hj
      obtain ⟨w, hw, hwv⟩ := exists_adj_of_edist_eq_succ hj.symm
      exact ⟨w, hwv.symm, by rw [edist_comm, hw]⟩
  · rintro (h | ⟨w, hvw, hw⟩)
    · exact h.trans (by exact_mod_cast Nat.le_succ t)
    · rw [edist_comm]
      calc G.edist v c ≤ G.edist v w + 1 := edist_le_add_one_of_adj hvw.symm
        _ ≤ t + 1 := by rw [edist_comm]; gcongr
        _ = ((t + 1 : ℕ) : ℕ∞) := by push_cast; rfl

end ClosedBall

/-! ### Closed neighbourhoods and dominating sets -/

section ClosedNeighbor

variable (G) in
/-- The closed neighbourhood `N⁺(v) = {v} ∪ N(v)`. -/
def closedNeighborSet (v : V) : Set V := insert v (G.neighborSet v)

variable {u v : V}

/-- Membership in the closed neighbourhood. -/
@[simp] lemma mem_closedNeighborSet : u ∈ G.closedNeighborSet v ↔ u = v ∨ G.Adj v u := .rfl

/-- A vertex lies in its closed neighbourhood. -/
lemma self_mem_closedNeighborSet (v : V) : v ∈ G.closedNeighborSet v := Set.mem_insert v _

/-- Closed neighbourhoods are symmetric. -/
lemma mem_closedNeighborSet_comm : u ∈ G.closedNeighborSet v ↔ v ∈ G.closedNeighborSet u := by
  simp only [mem_closedNeighborSet, adj_comm, eq_comm]

/-- The closed ball of radius one is the closed neighbourhood. -/
lemma closedBall_one (v : V) : G.closedBall v 1 = G.closedNeighborSet v := by
  ext u; simp [edist_le_one_iff_adj_or_eq, adj_comm, or_comm]

/-- The vertices at distance at most one form the closed neighbourhood. -/
lemma edist_le_one_iff_mem_closedNeighborSet : G.edist v u ≤ 1 ↔ u ∈ G.closedNeighborSet v := by
  rw [← closedBall_one, mem_closedBall']

variable (G) in
/-- The closed neighbourhood `N⁺(v)` as a `Finset`. -/
def closedNeighborFinset [DecidableEq V] (v : V) [Fintype (G.neighborSet v)] : Finset V :=
  insert v (G.neighborFinset v)

section Finset

variable [DecidableEq V] [Fintype (G.neighborSet v)]

/-- Membership in the closed neighbourhood `Finset`. -/
@[simp] lemma mem_closedNeighborFinset : u ∈ G.closedNeighborFinset v ↔ u = v ∨ G.Adj v u := by
  simp [closedNeighborFinset]

/-- The closed neighbourhood `Finset` as a set is the closed neighbourhood. -/
@[simp] lemma coe_closedNeighborFinset :
    (G.closedNeighborFinset v : Set V) = G.closedNeighborSet v := by
  ext u; simp

/-- The closed neighbourhood of `v` has `deg v + 1` vertices. -/
lemma card_closedNeighborFinset : (G.closedNeighborFinset v).card = G.degree v + 1 := by
  rw [closedNeighborFinset, Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree]

end Finset

variable (G) in
/-- `D` is a dominating set of `G`: every vertex is in `D` or adjacent to a vertex of `D`. -/
def IsDominatingSet (D : Set V) : Prop := ∀ v, v ∈ D ∨ ∃ u ∈ D, G.Adj v u

/-- `D` is dominating iff every closed neighbourhood meets `D`. -/
lemma isDominatingSet_iff_forall_exists_mem {D : Set V} :
    G.IsDominatingSet D ↔ ∀ v, ∃ u ∈ D, u ∈ G.closedNeighborSet v := by
  refine forall_congr' fun v => ?_
  simp only [mem_closedNeighborSet]
  constructor
  · rintro (h | ⟨u, hu, h⟩)
    · exact ⟨v, h, Or.inl rfl⟩
    · exact ⟨u, hu, Or.inr h⟩
  · rintro ⟨u, hu, rfl | h⟩
    · exact Or.inl hu
    · exact Or.inr ⟨u, hu, h⟩

/-- Supersets of dominating sets are dominating. -/
lemma IsDominatingSet.mono {D D' : Set V} (h : G.IsDominatingSet D) (hD : D ⊆ D') :
    G.IsDominatingSet D' :=
  fun v => (h v).imp (fun hv => hD hv) fun ⟨u, hu, huv⟩ => ⟨u, hD hu, huv⟩

/-- The set of all vertices is dominating. -/
@[simp] lemma isDominatingSet_univ : G.IsDominatingSet Set.univ := fun _ => Or.inl trivial

end ClosedNeighbor

/-! ### Lipschitz potentials -/

section Lipschitz

variable {f : V → ℕ} {a b : V}

/-- A potential growing by at most one along each edge grows by at most the length of a walk. -/
theorem Walk.le_add_length_of_lipschitz (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1)
    (w : G.Walk a b) : f b ≤ f a + w.length := by
  induction w with
  | nil => simp
  | cons h _ ih =>
    have := hf _ _ h
    simp only [Walk.length_cons]
    omega

/-- A potential growing by at most one along each edge gives lower bounds on distances:
`f b ≤ f a + d(a, b)` (extended-distance version). -/
theorem le_add_edist_of_lipschitz (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1) (a b : V) :
    (f b : ℕ∞) ≤ f a + G.edist a b := by
  by_cases h : G.Reachable a b
  · obtain ⟨w, hw⟩ := h.exists_walk_length_eq_edist
    rw [← hw]
    exact_mod_cast w.le_add_length_of_lipschitz hf
  · simp [edist_eq_top_of_not_reachable h]

/-- A potential growing by at most one along each edge gives lower bounds on distances:
`f b ≤ f a + d(a, b)` for connected `a`, `b`. -/
theorem Reachable.le_add_dist_of_lipschitz (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1)
    (h : G.Reachable a b) : f b ≤ f a + G.dist a b := by
  obtain ⟨w, hw⟩ := h.exists_walk_length_eq_dist
  rw [← hw]
  exact w.le_add_length_of_lipschitz hf

/-- A potential growing by at most one along each edge changes by at most `r` within distance
`r`. -/
theorem le_add_of_edist_le_of_lipschitz (hf : ∀ x y, G.Adj x y → f y ≤ f x + 1) {r : ℕ}
    (h : G.edist a b ≤ r) : f b ≤ f a + r := by
  have : (f b : ℕ∞) ≤ f a + r := (le_add_edist_of_lipschitz hf a b).trans (by gcongr)
  exact_mod_cast this

/-- A function constant along edges is constant along walks. -/
theorem Walk.apply_eq_of_forall_adj {β : Sort*} {g : V → β} (hg : ∀ x y, G.Adj x y → g x = g y)
    (w : G.Walk a b) : g a = g b := by
  induction w with
  | nil => rfl
  | cons h _ ih => exact (hg _ _ h).trans ih

/-- A function constant along edges is constant on connected pairs. -/
theorem Reachable.apply_eq_of_forall_adj {β : Sort*} {g : V → β}
    (hg : ∀ x y, G.Adj x y → g x = g y) (h : G.Reachable a b) : g a = g b :=
  h.elim (·.apply_eq_of_forall_adj hg)

end Lipschitz

/-! ### Closed balls in box products and in finite connected graphs -/

section BoxProd

variable {α β : Type*} {G₁ : SimpleGraph α} {G₂ : SimpleGraph β}

/-- A product of closed balls lies in the closed ball of the box product (radii add up). -/
theorem closedBall_prod_subset_closedBall_boxProd (x₁ : α) (x₂ : β) (r₁ r₂ : ℕ∞) :
    G₁.closedBall x₁ r₁ ×ˢ G₂.closedBall x₂ r₂ ⊆ (G₁ □ G₂).closedBall (x₁, x₂) (r₁ + r₂) := by
  rintro ⟨y₁, y₂⟩ ⟨h₁, h₂⟩
  rw [mem_closedBall, edist_boxProd]
  exact add_le_add h₁ h₂

/-- The first coordinate of a point of a closed ball of `G₁ □ G₂` lies in the closed ball of `G₁`
of the same radius. -/
theorem fst_mem_closedBall_of_mem_boxProd {x y : α × β} {r : ℕ∞}
    (h : y ∈ (G₁ □ G₂).closedBall x r) : y.1 ∈ G₁.closedBall x.1 r := by
  rw [mem_closedBall, edist_boxProd] at h
  exact le_self_add.trans h

/-- The second coordinate of a point of a closed ball of `G₁ □ G₂` lies in the closed ball of `G₂`
of the same radius. -/
theorem snd_mem_closedBall_of_mem_boxProd {x y : α × β} {r : ℕ∞}
    (h : y ∈ (G₁ □ G₂).closedBall x r) : y.2 ∈ G₂.closedBall x.2 r := by
  rw [mem_closedBall, edist_boxProd] at h
  exact le_add_self.trans h

/-- If all closed balls of radius `r₁` of `G₁` and of radius `r₂` of `G₂` are everything, then so
are the closed balls of radius `r₁ + r₂` of `G₁ □ G₂`. -/
theorem closedBall_boxProd_eq_univ {r₁ r₂ : ℕ∞} (h₁ : ∀ x, G₁.closedBall x r₁ = Set.univ)
    (h₂ : ∀ x, G₂.closedBall x r₂ = Set.univ) (x : α × β) :
    (G₁ □ G₂).closedBall x (r₁ + r₂) = Set.univ := by
  refine Set.eq_univ_of_univ_subset ?_
  rw [← Set.univ_prod_univ, ← h₁ x.1, ← h₂ x.2]
  exact closedBall_prod_subset_closedBall_boxProd _ _ _ _

end BoxProd

/-- In a preconnected graph on `n` vertices, every closed ball of radius `≥ n - 1` is the whole
vertex set. -/
theorem closedBall_eq_univ_of_preconnected [Fintype V] (hG : G.Preconnected) (x : V) {r : ℕ}
    (hr : Fintype.card V ≤ r + 1) : G.closedBall x r = Set.univ := by
  classical
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨p⟩ := hG y x
  have := p.bypass_isPath.length_lt
  exact (edist_le p.bypass).trans (by exact_mod_cast (by omega : p.bypass.length ≤ r))

end SimpleGraph
