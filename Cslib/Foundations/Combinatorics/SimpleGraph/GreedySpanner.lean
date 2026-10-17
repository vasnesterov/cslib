/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Foundations.Data.List.GreedyScan
public import Cslib.Foundations.Combinatorics.SimpleGraph.WeightedSpanner
public import Cslib.Foundations.Combinatorics.SimpleGraph.Girth
public import Cslib.Foundations.Combinatorics.SimpleGraph.Cycle

/-!
# The greedy spanner

The greedy `t`-spanner of Althöfer, Das, Dobkin, Joseph and Soares (1993): scan the edges of a
weighted graph `(G, w)` in non-decreasing order of weight and keep an edge `e = {u, v}` iff the
graph `H` of the edges kept so far has `d_H(u, v) > t · w(e)`.

## Main definitions

* `greedySpannerEdges w t L`: the edges kept when scanning the list `L` (a `List.greedyScan`).
* `greedySpanner w t L`: the graph of these edges.
* `IsGreedyOrder G w L`: `L` lists every edge of `G` exactly once, in non-decreasing weight order.
* `IsGreedySpanner G w t H`: `H` is the output of *some* execution (ties broken arbitrarily).

## Main statements

* The two properties of the scan used in all proofs: `lt_wlength_of_mem_greedySpannerEdges`
  (a kept edge is heavier than `t⁻¹ ×` every walk of earlier kept edges between its endpoints) and
  `exists_walk_of_not_mem_greedySpannerEdges` (a rejected edge is bypassed by such a walk of weight
  `≤ t · w(e)`).
* `IsGreedySpanner.isWSpanner`: the output is a `t`-spanner.
* `IsGreedySpanner.noShortCycles`: for `t ≥ 2k - 1` it has girth `> 2k`, hence (Moore bound)
  `O(n^{1+1/k})` edges.
* `IsGreedySpanner.forall_walk`: every rejected edge is bypassed by a walk of no heavier edges.
-/

@[expose] public section

open Finset
open scoped ENNReal NNReal

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {w : Sym2 V → ℝ≥0} {t : ℝ≥0}

open Classical in
/-- The edges kept by the greedy `t`-spanner algorithm scanning `L`: an edge `e` is kept iff
`t · w(e) < d_A(e)` for the graph `A` of the edges kept before it. -/
noncomputable def greedySpannerEdges (w : Sym2 V → ℝ≥0) (t : ℝ≥0) (L : List (Sym2 V)) :
    List (Sym2 V) :=
  L.greedyScan fun A e => (t : ℝ≥0∞) * w e < (fromEdgeSet {x | x ∈ A}).wdistS w e

/-- The greedy `t`-spanner algorithm run on the edge list `L`. -/
noncomputable def greedySpanner (w : Sym2 V → ℝ≥0) (t : ℝ≥0) (L : List (Sym2 V)) :
    SimpleGraph V :=
  fromEdgeSet {e | e ∈ greedySpannerEdges w t L}

/-- `L` lists the edges of `G`, each exactly once, in non-decreasing order of weight. -/
def IsGreedyOrder (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) (L : List (Sym2 V)) : Prop :=
  L.Nodup ∧ (∀ e, e ∈ L ↔ e ∈ G.edgeSet) ∧ L.Pairwise (fun a b => w a ≤ w b)

/-- `H` is (the output of an execution of) the greedy `t`-spanner of `(G, w)`. -/
def IsGreedySpanner (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) (t : ℝ≥0) (H : SimpleGraph V) :
    Prop :=
  ∃ L, IsGreedyOrder G w L ∧ H = greedySpanner w t L

/-- Every finite graph has an edge order as required by the greedy algorithm. -/
theorem exists_isGreedyOrder [Finite V] (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) :
    ∃ L, IsGreedyOrder G w L := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨L, hnd, hmem, hsort⟩ := (univ.filter (· ∈ G.edgeSet)).exists_list_nodup_pairwise_le w
  exact ⟨L, hnd, fun e => by simpa using hmem e, hsort⟩

/-- Every finite weighted graph has a greedy `t`-spanner. -/
theorem exists_isGreedySpanner [Finite V] (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) (t : ℝ≥0) :
    ∃ H, IsGreedySpanner G w t H :=
  let ⟨L, hL⟩ := exists_isGreedyOrder G w
  ⟨_, L, hL, rfl⟩

/-! ### The scan -/

/-- The step equation: Algorithm `Greedy(G, t)` as stated in the literature. -/
theorem greedySpannerEdges_concat (L : List (Sym2 V)) (e : Sym2 V) :
    greedySpannerEdges w t (L ++ [e]) =
      if (t : ℝ≥0∞) * w e < (greedySpanner w t L).wdistS w e then greedySpannerEdges w t L ++ [e]
      else greedySpannerEdges w t L := by
  classical
  rw [greedySpannerEdges, List.greedyScan_concat]
  rfl

/-- Kept edges are listed in `L`. -/
theorem mem_of_mem_greedySpannerEdges {L : List (Sym2 V)} {e : Sym2 V}
    (he : e ∈ greedySpannerEdges w t L) : e ∈ L :=
  List.mem_of_mem_greedyScan he

/-- The edges of the greedy spanner are kept edges. -/
theorem mem_greedySpannerEdges_of_mem_edgeSet {L : List (Sym2 V)} {e : Sym2 V}
    (he : e ∈ (greedySpanner w t L).edgeSet) : e ∈ greedySpannerEdges w t L := by
  rw [greedySpanner, edgeSet_fromEdgeSet] at he
  exact he.1

/-- If `L` lists only edges of `G`, the greedy spanner is a subgraph of `G`. -/
theorem greedySpanner_le {L : List (Sym2 V)} (hL : ∀ e ∈ L, e ∈ G.edgeSet) :
    greedySpanner w t L ≤ G := by
  intro u v huv
  rw [greedySpanner, fromEdgeSet_adj] at huv
  exact hL _ (mem_of_mem_greedySpannerEdges huv.1)

/-- The graph built while scanning a prefix of `L` is a subgraph of the output. -/
theorem greedySpanner_take_le (L : List (Sym2 V)) (i : ℕ) :
    greedySpanner w t (L.take i) ≤ greedySpanner w t L :=
  fromEdgeSet_mono fun _ he => (List.greedyScan_take_isPrefix L i).subset he

/-- **Key property of a kept edge.** If `{u, v}` was kept (`L` duplicate-free), then every walk
between `u` and `v` all of whose edges were kept *before* `{u, v}` weighs more than `t · w(uv)`. -/
theorem lt_wlength_of_mem_greedySpannerEdges [DecidableEq V] {L : List (Sym2 V)} (hL : L.Nodup)
    {u v : V} (he : s(u, v) ∈ greedySpannerEdges w t L) {G' : SimpleGraph V} (p : G'.Walk u v)
    (hp : ∀ f ∈ p.edges, f ∈ greedySpannerEdges w t L ∧ L.idxOf f < L.idxOf s(u, v)) :
    (t : ℝ≥0∞) * w s(u, v) < p.wlength w := by
  classical
  have hacc := List.keep_of_mem_greedyScan hL he
  rw [wdistS_mk] at hacc
  have hsub : ∀ f ∈ p.edges, f ∈ (greedySpanner w t (L.take (L.idxOf s(u, v)))).edgeSet := by
    intro f hf
    obtain ⟨hfA, hfi⟩ := hp f hf
    rw [greedySpanner, edgeSet_fromEdgeSet]
    refine ⟨(List.mem_greedyScan_take_iff hL).2
      ⟨hfA, (List.mem_take_iff_idxOf_lt (mem_of_mem_greedySpannerEdges hfA)).2 hfi⟩, ?_⟩
    exact G'.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet hf)
  calc (t : ℝ≥0∞) * w s(u, v) < _ := hacc
    _ ≤ (p.transfer _ hsub).wlength w := wdist_le _
    _ = p.wlength w := Walk.wlength_transfer w p hsub

/-- **Key property of a rejected edge.** If `L[i] = {u, v}` was not kept, then `u` and `v` are
joined by a walk of edges kept before position `i`, of total weight at most `t · w(uv)`. -/
theorem exists_walk_of_not_mem_greedySpannerEdges [Finite V] {L : List (Sym2 V)} {i : ℕ}
    (hi : i < L.length) {u v : V} (hLi : L[i] = s(u, v))
    (hrej : s(u, v) ∉ greedySpannerEdges w t L) :
    ∃ p : (greedySpanner w t (L.take i)).Walk u v, p.wlength w ≤ t * w s(u, v) := by
  classical
  have hno : ¬ ((t : ℝ≥0∞) * w s(u, v) < (greedySpanner w t (L.take i)).wdist w u v) := by
    intro hacc
    refine hrej (hLi ▸ List.getElem_mem_greedyScan hi ?_)
    rw [hLi]
    exact hacc
  rw [not_lt] at hno
  obtain ⟨p, -, hp⟩ := exists_isPath_wlength_eq (w := w) (reachable_of_wdist_lt_top
    (hno.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top)))
  exact ⟨p, hp ▸ hno⟩

/-! ### The greedy spanner is a spanner -/

/-- Every listed edge is stretched by at most `t` in the output. -/
theorem greedySpanner_wdist_le_of_mem [Finite V] {L : List (Sym2 V)} (ht : 1 ≤ t) {u v : V}
    (huvL : s(u, v) ∈ L) : (greedySpanner w t L).wdist w u v ≤ t * w s(u, v) := by
  classical
  by_cases hmem : s(u, v) ∈ greedySpannerEdges w t L
  · by_cases huv : u = v
    · subst huv
      simp
    · calc (greedySpanner w t L).wdist w u v ≤ w s(u, v) :=
            wdist_le_of_adj ((fromEdgeSet_adj _).mpr ⟨hmem, huv⟩)
        _ ≤ t * w s(u, v) := le_mul_of_one_le_left zero_le (by exact_mod_cast ht)
  · have hi : L.idxOf s(u, v) < L.length := List.idxOf_lt_length_of_mem huvL
    obtain ⟨p, hp⟩ := exists_walk_of_not_mem_greedySpannerEdges hi (List.getElem_idxOf hi) hmem
    calc (greedySpanner w t L).wdist w u v ≤ (p.mapLe (greedySpanner_take_le L _)).wlength w :=
          wdist_le _
      _ = p.wlength w := Walk.wlength_mapLe w _ p
      _ ≤ t * w s(u, v) := hp

/-- **The greedy `t`-spanner is a `t`-spanner.** -/
theorem IsGreedySpanner.isWSpanner [Finite V] (ht : 1 ≤ t) (hH : IsGreedySpanner G w t H) :
    IsWSpanner G H w t := by
  obtain ⟨L, ⟨-, hLG, -⟩, rfl⟩ := hH
  exact isWSpanner_of_adj ht (greedySpanner_le fun e he => (hLG e).mp he)
    fun x y hxy => greedySpanner_wdist_le_of_mem ht ((hLG _).mpr hxy)

/-- Every edge of `G` rejected by the greedy algorithm is bypassed in `H` by a walk of edges that
were examined earlier, hence are not heavier. -/
theorem IsGreedySpanner.forall_walk [Finite V] (hH : IsGreedySpanner G w t H) :
    H ≤ G ∧ ∀ u v, G.Adj u v → ¬ H.Adj u v → ∃ p : H.Walk u v, ∀ f ∈ p.edges, w f ≤ w s(u, v) := by
  classical
  obtain ⟨L, ⟨hnd, hLG, hsort⟩, rfl⟩ := hH
  refine ⟨greedySpanner_le fun e he => (hLG e).mp he, fun u v huv hnH => ?_⟩
  have huvL : s(u, v) ∈ L := (hLG _).mpr huv
  have hi : L.idxOf s(u, v) < L.length := List.idxOf_lt_length_of_mem huvL
  have hrej : s(u, v) ∉ greedySpannerEdges w t L := fun h =>
    hnH ((fromEdgeSet_adj _).mpr ⟨h, huv.ne⟩)
  obtain ⟨p, -⟩ := exists_walk_of_not_mem_greedySpannerEdges hi (List.getElem_idxOf hi) hrej
  refine ⟨p.mapLe (greedySpanner_take_le L _), fun f hf => ?_⟩
  rw [Walk.edges_mapLe_eq_edges] at hf
  have hf' := p.edges_subset_edgeSet hf
  rw [greedySpanner, edgeSet_fromEdgeSet] at hf'
  obtain ⟨hfA, hfi⟩ := (List.mem_greedyScan_take_iff hnd).1 hf'.1
  have hfL : f ∈ L := mem_of_mem_greedySpannerEdges hfA
  exact hsort.rel_of_idxOf_lt hfL huvL ((List.mem_take_iff_idxOf_lt hfL).mp hfi)

/-- **Girth.** For `t ≥ 2k - 1` the greedy `t`-spanner has no cycle of length `≤ 2k`: the edge of
such a cycle examined last would be bypassed by the rest of the cycle, of weight
`≤ (2k - 1) · w(e)`. -/
theorem IsGreedySpanner.noShortCycles {k : ℕ} (ht : ((2 * k - 1 : ℕ) : ℝ≥0) ≤ t)
    (hH : IsGreedySpanner G w t H) : H.NoShortCycles (2 * k) := by
  classical
  obtain ⟨L, ⟨hnd, hLG, hsort⟩, rfl⟩ := hH
  intro v c hc
  by_contra hlen
  push Not at hlen
  have hA : ∀ f ∈ c.edges, f ∈ greedySpannerEdges w t L := fun f hf =>
    mem_greedySpannerEdges_of_mem_edgeSet (c.edges_subset_edgeSet hf)
  have hinL : ∀ f ∈ c.edges, f ∈ L := fun f hf => mem_of_mem_greedySpannerEdges (hA f hf)
  have hne : c.edges.toFinset.Nonempty := by
    cases c with
    | nil => exact absurd hc (by simp [Walk.isCycle_def])
    | cons h p => exact ⟨_, List.mem_toFinset.mpr (List.mem_cons_self ..)⟩
  obtain ⟨e, heS, hemax⟩ := c.edges.toFinset.exists_max_image (L.idxOf ·) hne
  rw [List.mem_toFinset] at heS
  induction e using Sym2.ind with
  | _ a b =>
  obtain ⟨p, -, hpe, -, hpl⟩ := hc.exists_path_of_mem_edges heS
  have hlt : ∀ f ∈ p.edges, L.idxOf f < L.idxOf s(a, b) := fun f hf =>
    lt_of_le_of_ne (hemax f (List.mem_toFinset.mpr (hpe f hf).1))
      (fun h => (hpe f hf).2 ((List.idxOf_inj (hinL f (hpe f hf).1)).mp h))
  have key := lt_wlength_of_mem_greedySpannerEdges hnd (hA _ heS) p
    fun f hf => ⟨hA f (hpe f hf).1, hlt f hf⟩
  have hw : p.wlength w ≤ p.length * (w s(a, b) : ℝ≥0∞) := p.wlength_le_length_mul w fun f hf => by
    exact_mod_cast hsort.rel_of_idxOf_lt (hinL f (hpe f hf).1) (hinL _ heS) (hlt f hf)
  have hplen : (p.length : ℝ≥0∞) ≤ t := by
    have : p.length ≤ 2 * k - 1 := by omega
    calc (p.length : ℝ≥0∞) ≤ ((2 * k - 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast this
      _ ≤ t := by exact_mod_cast ht
  exact absurd (hw.trans (by gcongr)) (not_le.mpr key)

end SimpleGraph
