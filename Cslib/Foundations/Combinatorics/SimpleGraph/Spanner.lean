/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Tactic.Ring

/-!
# Spanners and fault-tolerant spanners (unweighted)

* `G.deleteVerts F` — the graph `G \ F` for a vertex set `F`, as a graph on the *same* vertex type:
  every edge touching `F` is removed (the vertices of `F` become isolated). For `u v ∉ F`,
  distances in `G.deleteVerts F` are exactly distances in the induced subgraph `G[V \ F]`.
* `ediam_le_coe_iff` — `G.ediam ≤ t` iff any two vertices are joined by a walk of length `≤ t`.
* `Walk.interior p` — the vertices of a `u`–`v` walk other than `u`, `v`.
* Length-bounded cuts: `lt_edist_deleteVerts_iff` / `lt_edist_deleteEdges_iff` characterize
  `t < d_{G \ F}(u, v)` as "`F` hits every `u`–`v` walk of length `≤ t`".
* `IsSpanner`, `IsVFTSpanner` (vertex faults), `IsEFTSpanner` (edge faults), with distances `edist`
  in `ℕ∞` (`⊤` = unreachable).
* `edist_le_mul_of_adj` — the local criterion: if every edge `xy` of `G` has `d_H(x, y) ≤ t`, then
  `d_H ≤ t · d_G` everywhere; `isVFTSpanner_iff` / `isEFTSpanner_iff` (unweighted Lemma 3 of
  Dinitz–Robelle, PODC'20).
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V}

/-! ### Vertex deletion -/

/-- `G \ F`: remove all edges incident to a vertex of `F` (the vertices stay, isolated). -/
def deleteVerts (G : SimpleGraph V) (F : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ F ∧ v ∉ F
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

@[simp] lemma deleteVerts_adj {F : Set V} {u v : V} :
    (G.deleteVerts F).Adj u v ↔ G.Adj u v ∧ u ∉ F ∧ v ∉ F := Iff.rfl

lemma deleteVerts_le (G : SimpleGraph V) (F : Set V) : G.deleteVerts F ≤ G := fun _ _ h => h.1

lemma deleteVerts_mono {F : Set V} (h : G ≤ H) : G.deleteVerts F ≤ H.deleteVerts F :=
  fun _ _ hh => ⟨h hh.1, hh.2⟩

lemma deleteVerts_anti {F F' : Set V} (h : F ⊆ F') : G.deleteVerts F' ≤ G.deleteVerts F :=
  fun _ _ hh => ⟨hh.1, fun hu => hh.2.1 (h hu), fun hv => hh.2.2 (h hv)⟩

@[simp] lemma deleteVerts_empty : G.deleteVerts ∅ = G := by ext; simp

namespace Walk

/-- A walk of `G` avoiding `F` is a walk of `G.deleteVerts F`. -/
def toDeleteVerts {F : Set V} {u v : V} (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∉ F) :
    (G.deleteVerts F).Walk u v :=
  p.transfer _ (by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      exact ⟨p.adj_of_mem_edges he, hp _ (p.fst_mem_support_of_mem_edges he),
        hp _ (p.snd_mem_support_of_mem_edges he)⟩)

@[simp] lemma length_toDeleteVerts {F : Set V} {u v : V} (p : G.Walk u v) (hp) :
    (p.toDeleteVerts (F := F) hp).length = p.length := length_transfer _ _

@[simp] lemma support_toDeleteVerts {F : Set V} {u v : V} (p : G.Walk u v) (hp) :
    (p.toDeleteVerts (F := F) hp).support = p.support := support_transfer _ _

/-- All vertices of a walk in `G \ F` starting outside `F` lie outside `F`. -/
lemma not_mem_of_mem_support_deleteVerts {F : Set V} {u v : V}
    (p : (G.deleteVerts F).Walk u v) (hu : u ∉ F) : ∀ x ∈ p.support, x ∉ F := by
  induction p with
  | nil => simpa using hu
  | cons h q ih =>
    intro x hx
    rw [support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hu
    · exact ih h.2.2 x hx

/-- The interior of a `u`–`v` walk: its vertices other than `u` and `v`. -/
def interior [DecidableEq V] {u v : V} (p : G.Walk u v) : Finset V :=
  p.support.toFinset \ {u, v}

lemma mem_interior [DecidableEq V] {u v x : V} {p : G.Walk u v} :
    x ∈ p.interior ↔ x ∈ p.support ∧ x ≠ u ∧ x ≠ v := by
  simp [interior]

lemma interior_mapLe [DecidableEq V] {G' : SimpleGraph V} (h : G ≤ G') {u v : V}
    (p : G.Walk u v) : (p.mapLe h).interior = p.interior := by
  simp [interior]

lemma card_interior_le [DecidableEq V] {u v : V} (p : G.Walk u v) : #p.interior ≤ p.length := by
  have h1 : #p.interior ≤ #(p.support.toFinset.erase u) := by
    apply card_le_card
    intro x hx
    rw [mem_interior] at hx
    simp [hx.1, hx.2.1]
  have h2 : #(p.support.toFinset.erase u) + 1 = #p.support.toFinset :=
    card_erase_add_one (by simp)
  have h3 : #p.support.toFinset ≤ p.length + 1 := by
    simpa using List.toFinset_card_le p.support
  omega

lemma card_edges_toFinset_le [DecidableEq V] {u v : V} (p : G.Walk u v) :
    #p.edges.toFinset ≤ p.length := by
  simpa using List.toFinset_card_le p.edges

end Walk

/-! ### Distances -/

lemma edist_le_coe_iff {u v : V} {t : ℕ} :
    G.edist u v ≤ t ↔ ∃ p : G.Walk u v, p.length ≤ t := by
  constructor
  · intro h
    have hne : G.edist u v ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top t) h
    obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top hne
    exact ⟨p, by rw [← hp] at h; exact_mod_cast h⟩
  · rintro ⟨p, hp⟩
    exact (edist_le p).trans (by exact_mod_cast hp)

/-- A graph has (extended) diameter at most `t` iff any two vertices are joined by a walk of length
at most `t`. -/
lemma ediam_le_coe_iff {t : ℕ} : G.ediam ≤ t ↔ ∀ u v, ∃ p : G.Walk u v, p.length ≤ t := by
  simp only [ediam_le_iff, edist_le_coe_iff]

/-- **Vertex length-bounded cuts.** For `u, v ∉ F`, `d_{G \ F}(u, v) > t` iff every `u`–`v` walk of
`G` of length `≤ t` has an interior vertex in `F`. -/
theorem lt_edist_deleteVerts_iff [DecidableEq V] {F : Finset V} {u v : V} (hu : u ∉ F)
    (hv : v ∉ F) {t : ℕ} :
    (t : ℕ∞) < (G.deleteVerts F).edist u v ↔
      ∀ p : G.Walk u v, p.length ≤ t → ¬ Disjoint p.interior F := by
  rw [← not_le, edist_le_coe_iff, not_iff_comm, not_forall]
  simp only [not_imp, not_not]
  constructor
  · rintro ⟨p, hpt, hpF⟩
    have hsupp : ∀ x ∈ p.support, x ∉ (F : Set V) := by
      intro x hx hxF
      by_cases hxu : x = u
      · exact hu (hxu ▸ hxF)
      by_cases hxv : x = v
      · exact hv (hxv ▸ hxF)
      exact Finset.disjoint_left.mp hpF (Walk.mem_interior.mpr ⟨hx, hxu, hxv⟩) hxF
    exact ⟨p.toDeleteVerts hsupp, by simpa using hpt⟩
  · rintro ⟨p, hpt⟩
    refine ⟨p.mapLe (G.deleteVerts_le _), by simpa using hpt, ?_⟩
    rw [Finset.disjoint_left]
    intro x hx hxF
    have hx' : x ∈ p.support := by
      have := (Walk.mem_interior.mp hx).1
      simpa using this
    exact p.not_mem_of_mem_support_deleteVerts (by simpa using hu) x hx' (by simpa using hxF)

/-- **Edge length-bounded cuts.** `d_{G \ F}(u, v) > t` iff every `u`–`v` walk of `G` of length
`≤ t` uses an edge of `F`. -/
theorem lt_edist_deleteEdges_iff [DecidableEq V] {F : Finset (Sym2 V)} {u v : V} {t : ℕ} :
    (t : ℕ∞) < (G.deleteEdges F).edist u v ↔
      ∀ p : G.Walk u v, p.length ≤ t → ¬ Disjoint p.edges.toFinset F := by
  rw [← not_le, edist_le_coe_iff, not_iff_comm, not_forall]
  simp only [not_imp, not_not]
  constructor
  · rintro ⟨p, hpt, hpF⟩
    refine ⟨p.toDeleteEdges F (fun e he heF => ?_), by simpa using hpt⟩
    exact Finset.disjoint_left.mp hpF (List.mem_toFinset.mpr he) heF
  · rintro ⟨p, hpt⟩
    refine ⟨p.mapLe (G.deleteEdges_le _), by simpa using hpt, ?_⟩
    rw [Finset.disjoint_left]
    intro e he heF
    rw [List.mem_toFinset, Walk.edges_mapLe_eq_edges] at he
    have := p.edges_subset_edgeSet he
    rw [edgeSet_deleteEdges] at this
    exact this.2 heF

/-- **Local criterion for stretch.** If every edge `xy` of `G` satisfies `d_H(x, y) ≤ t`, then
`d_H(u, v) ≤ t · d_G(u, v)` for all `u, v`. -/
theorem edist_le_mul_of_adj {t : ℕ} (ht : 1 ≤ t) (h : ∀ x y, G.Adj x y → H.edist x y ≤ t)
    (u v : V) : H.edist u v ≤ t * G.edist u v := by
  by_cases hr : G.Reachable u v
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    rw [← hp]
    clear hp hr
    induction p with
    | nil => simp
    | @cons x y z hxy q ih =>
      calc H.edist x z ≤ H.edist x y + H.edist y z := H.edist_triangle
        _ ≤ t + t * q.length := add_le_add (h _ _ hxy) ih
        _ = t * (q.cons hxy).length := by
          rw [Walk.length_cons]; push_cast; ring
  · rw [edist_eq_top_of_not_reachable hr, ENat.mul_top (by exact_mod_cast (by omega : t ≠ 0))]
    exact le_top

/-! ### Spanners -/

/-- `H` is a `t`-spanner of `G`: a subgraph with `d_H(u, v) ≤ t · d_G(u, v)` for all `u, v`. -/
def IsSpanner (G H : SimpleGraph V) (t : ℕ) : Prop :=
  H ≤ G ∧ ∀ u v, H.edist u v ≤ t * G.edist u v

/-- `H` is an `f`-vertex-fault-tolerant `t`-spanner of `G` (Definition 1 of Dinitz–Robelle):
for every fault set `F` of at most `f` vertices and all `u, v ∉ F`,
`d_{H \ F}(u, v) ≤ t · d_{G \ F}(u, v)`. -/
def IsVFTSpanner (G H : SimpleGraph V) (f t : ℕ) : Prop :=
  H ≤ G ∧ ∀ F : Finset V, #F ≤ f → ∀ u v, u ∉ F → v ∉ F →
    (H.deleteVerts F).edist u v ≤ t * (G.deleteVerts F).edist u v

/-- `H` is an `f`-edge-fault-tolerant `t`-spanner of `G`: for every set `F` of at most `f` edges,
`d_{H \ F}(u, v) ≤ t · d_{G \ F}(u, v)` for all `u, v`. -/
def IsEFTSpanner (G H : SimpleGraph V) (f t : ℕ) : Prop :=
  H ≤ G ∧ ∀ F : Finset (Sym2 V), #F ≤ f → ∀ u v,
    (H.deleteEdges F).edist u v ≤ t * (G.deleteEdges F).edist u v

lemma IsVFTSpanner.isSpanner {f t : ℕ} (h : IsVFTSpanner G H f t) : IsSpanner G H t :=
  ⟨h.1, fun u v => by simpa using h.2 ∅ (by simp) u v (by simp) (by simp)⟩

lemma IsEFTSpanner.isSpanner {f t : ℕ} (h : IsEFTSpanner G H f t) : IsSpanner G H t :=
  ⟨h.1, fun u v => by simpa using h.2 ∅ (by simp) u v⟩

/-- **Lemma 3 of Dinitz–Robelle (unweighted, vertex faults).** It suffices to check edges:
`H ≤ G` is an `f`-VFT `t`-spanner iff for every fault set `F` with `|F| ≤ f` and every edge `uv`
of `G` with `u, v ∉ F`, `d_{H \ F}(u, v) ≤ t`. -/
theorem isVFTSpanner_iff {f t : ℕ} (ht : 1 ≤ t) (hHG : H ≤ G) :
    IsVFTSpanner G H f t ↔ ∀ F : Finset V, #F ≤ f → ∀ u v, G.Adj u v → u ∉ F → v ∉ F →
      (H.deleteVerts F).edist u v ≤ t := by
  constructor
  · intro h F hF u v huv hu hv
    have := h.2 F hF u v hu hv
    have h1 : (G.deleteVerts F).edist u v = 1 := by
      rw [edist_eq_one_iff_adj]; exact ⟨huv, hu, hv⟩
    simpa [h1] using this
  · intro h
    refine ⟨hHG, fun F hF u v _ _ => ?_⟩
    apply edist_le_mul_of_adj ht
    intro x y hxy
    exact h F hF x y hxy.1 hxy.2.1 hxy.2.2

/-- Edge-fault version of `isVFTSpanner_iff`. -/
theorem isEFTSpanner_iff {f t : ℕ} (ht : 1 ≤ t) (hHG : H ≤ G) :
    IsEFTSpanner G H f t ↔ ∀ F : Finset (Sym2 V), #F ≤ f → ∀ u v, G.Adj u v → s(u, v) ∉ F →
      (H.deleteEdges F).edist u v ≤ t := by
  constructor
  · intro h F hF u v huv huvF
    have := h.2 F hF u v
    have h1 : (G.deleteEdges F).edist u v = 1 := by
      rw [edist_eq_one_iff_adj, deleteEdges_adj]; exact ⟨huv, by simpa using huvF⟩
    simpa [h1] using this
  · intro h
    refine ⟨hHG, fun F hF u v => ?_⟩
    apply edist_le_mul_of_adj ht
    intro x y hxy
    rw [deleteEdges_adj] at hxy
    exact h F hF x y hxy.1 (by simpa using hxy.2)

end SimpleGraph
