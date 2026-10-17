/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Foundations.Data.List.GreedyScan
public import Cslib.Foundations.Combinatorics.SimpleGraph.WeightedSpanner
public import Cslib.Foundations.Combinatorics.SimpleGraph.BlockingSet
public import Cslib.Foundations.Combinatorics.SimpleGraph.Cycle

/-!
# Greedy schemes for fault-tolerant spanners

The fault-tolerant greedy algorithms (Bodwin–Dinitz–Parter–Williams; Bodwin–Patel, PODC'19;
Dinitz–Robelle, PODC'20) scan a list `L` of edges, given as ordered pairs `(u, v)`, and add the edge
`(u, v)` to the current graph `H` iff a decision procedure `dec H u v` answers YES (typically: "some
small fault set stretches `d_H(u, v)` too much").

## Main definitions

* `edgeGraph A`: the graph whose edges are the pairs of the list `A` (loops dropped).
* `greedyEdges dec L`: the pairs added by the scan, in insertion order (a `List.greedyScan`);
  `greedyGraph dec L = edgeGraph (greedyEdges dec L)`: the output.

## Main statements

* `greedyEdges_concat`: the step equation (the algorithm as stated in the papers).
* `mem_greedyEdges_or_reject`: every entry of `L` was added, or rejected by `dec` on the graph of
  the entries added before it; `dec_greedyEdges_take`: every added entry was accepted.
* Correctness, for weighted graphs (`greedyGraph_isWeightedVFTSpanner`,
  `greedyGraph_isWeightedEFTSpanner`: a rejection must certify `d_{H \ F}(u, v) ≤ t · w(uv)` on the
  graph built so far) and unweighted graphs (`greedyGraph_isVFTSpanner`,
  `greedyGraph_isEFTSpanner`, via unit weights).
* `exists_blockingSet_of_insertion`: if every added edge `(u, v)` comes with a set of `≤ D`
  vertices avoiding `u, v` that hits every short `u`–`v` walk of earlier edges, then the output has
  a blocking set of size `≤ D · |E|` (the size analysis of all fault-tolerant greedy algorithms).
* `exists_sorted_edgeList`: valid inputs exist (every edge listed, sorted by weight).
-/

@[expose] public section

open Finset
open scoped ENNReal NNReal

namespace SimpleGraph

variable {V : Type*}

/-! ### Graphs given by lists of pairs -/

/-- The graph whose edges are the pairs of `A` (loops are dropped). -/
def edgeGraph (A : List (V × V)) : SimpleGraph V :=
  fromEdgeSet {e | ∃ p ∈ A, s(p.1, p.2) = e}

/-- Adjacency in `edgeGraph A`: distinct endpoints of a pair of `A` (in either order). -/
theorem edgeGraph_adj {A : List (V × V)} {u v : V} :
    (edgeGraph A).Adj u v ↔ u ≠ v ∧ ∃ p ∈ A, s(p.1, p.2) = s(u, v) := by
  simp [edgeGraph, and_comm]

/-- The edges of `edgeGraph A` are the non-loop pairs of `A`. -/
theorem mem_edgeSet_edgeGraph {A : List (V × V)} {e : Sym2 V} :
    e ∈ (edgeGraph A).edgeSet ↔ (∃ p ∈ A, s(p.1, p.2) = e) ∧ ¬ e.IsDiag := by
  simp [edgeGraph]

/-- `edgeGraph` is monotone in the list of pairs. -/
theorem edgeGraph_mono {A A' : List (V × V)} (h : A ⊆ A') : edgeGraph A ≤ edgeGraph A' := by
  intro u v huv
  rw [edgeGraph_adj] at huv ⊢
  obtain ⟨hne, p, hp, hpe⟩ := huv
  exact ⟨hne, p, h hp, hpe⟩

/-- If all pairs of `A` are edges of `G`, then `edgeGraph A ≤ G`. -/
theorem edgeGraph_le {G : SimpleGraph V} {A : List (V × V)} (h : ∀ p ∈ A, G.Adj p.1 p.2) :
    edgeGraph A ≤ G := by
  intro u v huv
  rw [edgeGraph_adj] at huv
  obtain ⟨-, p, hp, hpe⟩ := huv
  have := h p hp
  rw [← mem_edgeSet, hpe] at this
  exact this

/-- A non-loop pair of `A` is an edge of `edgeGraph A`. -/
theorem edgeGraph_adj_of_mem {A : List (V × V)} {p : V × V} (hp : p ∈ A) (hne : p.1 ≠ p.2) :
    (edgeGraph A).Adj p.1 p.2 :=
  edgeGraph_adj.mpr ⟨hne, p, hp, rfl⟩

/-! ### The greedy scheme -/

/-- The pairs added by the greedy scheme with decision procedure `dec`, in insertion order: the
pair `(u, v)` is added iff `dec H u v` answers YES on the graph `H` of the pairs added before. -/
def greedyEdges (dec : SimpleGraph V → V → V → Bool) (L : List (V × V)) : List (V × V) :=
  L.greedyScan fun A p => dec (edgeGraph A) p.1 p.2 = true

/-- The output of the greedy scheme with decision procedure `dec` on the edge list `L`. -/
def greedyGraph (dec : SimpleGraph V → V → V → Bool) (L : List (V × V)) : SimpleGraph V :=
  edgeGraph (greedyEdges dec L)

variable {dec : SimpleGraph V → V → V → Bool}

/-- The step equation: scanning one more pair `p` adds it iff `dec` accepts it on the current
graph. -/
theorem greedyEdges_concat (L : List (V × V)) (p : V × V) :
    greedyEdges dec (L ++ [p]) =
      if dec (greedyGraph dec L) p.1 p.2 then greedyEdges dec L ++ [p] else greedyEdges dec L :=
  List.greedyScan_concat _ L p

/-- The added pairs form a sublist of `L`. -/
theorem greedyEdges_sublist (L : List (V × V)) : (greedyEdges dec L).Sublist L := by
  unfold greedyEdges; exact List.greedyScan_sublist L

/-- Added pairs are entries of `L`. -/
theorem mem_of_mem_greedyEdges {L : List (V × V)} {p : V × V} (h : p ∈ greedyEdges dec L) :
    p ∈ L :=
  (greedyEdges_sublist L).subset h

/-- Every added pair was accepted by `dec` on the graph of the pairs added before it. -/
theorem dec_greedyEdges_take (L : List (V × V)) (i : ℕ) (h : i < (greedyEdges dec L).length) :
    dec (edgeGraph ((greedyEdges dec L).take i)) (greedyEdges dec L)[i].1
      (greedyEdges dec L)[i].2 = true := by
  unfold greedyEdges; exact List.keep_take_greedyScan L i h

/-- Every entry `p ∈ L` is added, or rejected by `dec` at some position `i` on the graph of the
pairs added before (in particular a subgraph of the output). -/
theorem mem_greedyEdges_or_reject {L : List (V × V)} {p : V × V} (hp : p ∈ L) :
    p ∈ greedyEdges dec L ∨ ∃ i, ∃ hi : i < L.length, L[i] = p ∧
      dec (edgeGraph (greedyEdges dec (L.take i))) p.1 p.2 = false := by
  have := List.mem_greedyScan_or_not_keep (keep := fun A p => dec (edgeGraph A) p.1 p.2 = true) hp
  simp only [Bool.not_eq_true] at this
  exact this

/-- The graph built while scanning a prefix of `L` is a subgraph of the output. -/
theorem edgeGraph_greedyEdges_take_le (L : List (V × V)) (i : ℕ) :
    edgeGraph (greedyEdges dec (L.take i)) ≤ greedyGraph dec L := by
  exact edgeGraph_mono (List.greedyScan_take_isPrefix
    (keep := fun A p => dec (edgeGraph A) p.1 p.2 = true) L i).subset

/-- If `L` lists only edges of `G`, the output is a subgraph of `G`. -/
theorem greedyGraph_le {G : SimpleGraph V} {L : List (V × V)} (hLG : ∀ p ∈ L, G.Adj p.1 p.2) :
    greedyGraph dec L ≤ G :=
  edgeGraph_le fun p hp => hLG p (mem_of_mem_greedyEdges hp)

/-! ### Correctness -/

/-- **Correctness of the greedy scheme (weighted, vertex faults).** Suppose that whenever the
entry `L[i] = (u, v)` is rejected, every fault set `F ∌ u, v` with `|F| ≤ f` leaves
`d_{H_i \ F}(u, v) ≤ t · w(uv)` in the graph `H_i` built so far. Then the output is an `f`-VFT
`t`-spanner of `(G, w)`. -/
theorem greedyGraph_isWeightedVFTSpanner {G : SimpleGraph V} {w : Sym2 V → ℝ≥0}
    {L : List (V × V)} {f t : ℕ} (ht : 1 ≤ t)
    (hrej : ∀ i (hi : i < L.length),
      dec (edgeGraph (greedyEdges dec (L.take i))) L[i].1 L[i].2 = false →
      ∀ F : Finset V, #F ≤ f → L[i].1 ∉ F → L[i].2 ∉ F →
        ((edgeGraph (greedyEdges dec (L.take i))).deleteVerts F).wdist w L[i].1 L[i].2 ≤
          t * w s(L[i].1, L[i].2))
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) :
    IsWeightedVFTSpanner G (greedyGraph dec L) w f t := by
  refine isWeightedVFTSpanner_of_adj ht (greedyGraph_le hLG) fun F hF u v huv hu hv => ?_
  have key : ∀ p ∈ L, p.1 ∉ F → p.2 ∉ F →
      ((greedyGraph dec L).deleteVerts F).wdist w p.1 p.2 ≤ t * w s(p.1, p.2) := by
    intro p hp h1 h2
    rcases mem_greedyEdges_or_reject hp with hmem | ⟨i, hi, rfl, hno⟩
    · refine (wdist_le_of_adj (G := (greedyGraph dec L).deleteVerts F)
        ⟨edgeGraph_adj_of_mem hmem (hLG _ hp).ne, h1, h2⟩).trans ?_
      exact le_mul_of_one_le_left zero_le (by exact_mod_cast ht)
    · exact (wdist_anti (deleteVerts_mono (edgeGraph_greedyEdges_take_le L i))).trans
        (hrej i hi hno F hF h1 h2)
  rcases hL u v huv with h | h
  · exact key _ h hu hv
  · rw [wdist_comm, Sym2.eq_swap]; exact key _ h hv hu

/-- **Correctness of the greedy scheme (weighted, edge faults).** -/
theorem greedyGraph_isWeightedEFTSpanner {G : SimpleGraph V} {w : Sym2 V → ℝ≥0}
    {L : List (V × V)} {f t : ℕ} (ht : 1 ≤ t)
    (hrej : ∀ i (hi : i < L.length),
      dec (edgeGraph (greedyEdges dec (L.take i))) L[i].1 L[i].2 = false →
      ∀ F : Finset (Sym2 V), #F ≤ f → s(L[i].1, L[i].2) ∉ F →
        ((edgeGraph (greedyEdges dec (L.take i))).deleteEdges F).wdist w L[i].1 L[i].2 ≤
          t * w s(L[i].1, L[i].2))
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) :
    IsWeightedEFTSpanner G (greedyGraph dec L) w f t := by
  refine isWeightedEFTSpanner_of_adj ht (greedyGraph_le hLG) fun F hF u v huv huvF => ?_
  have key : ∀ p ∈ L, s(p.1, p.2) ∉ F →
      ((greedyGraph dec L).deleteEdges F).wdist w p.1 p.2 ≤ t * w s(p.1, p.2) := by
    intro p hp hpF
    rcases mem_greedyEdges_or_reject hp with hmem | ⟨i, hi, rfl, hno⟩
    · have hadj : ((greedyGraph dec L).deleteEdges F).Adj p.1 p.2 := by
        rw [deleteEdges_adj]
        exact ⟨edgeGraph_adj_of_mem hmem (hLG _ hp).ne, by simpa using hpF⟩
      refine (wdist_le_of_adj hadj).trans ?_
      exact le_mul_of_one_le_left zero_le (by exact_mod_cast ht)
    · exact (wdist_anti (deleteEdges_mono (edgeGraph_greedyEdges_take_le L i))).trans
        (hrej i hi hno F hF hpF)
  rcases hL u v huv with h | h
  · exact key _ h huvF
  · rw [wdist_comm, Sym2.eq_swap]; exact key _ h (by rwa [Sym2.eq_swap])

/-- **Correctness of the greedy scheme (unweighted, vertex faults).** If `dec H u v` answers NO
only when `d_{H \ F}(u, v) ≤ t` for every fault set `F ∌ u, v` with `|F| ≤ f`, then the output is
an `f`-VFT `t`-spanner. -/
theorem greedyGraph_isVFTSpanner {G : SimpleGraph V} {L : List (V × V)} {f t : ℕ} (ht : 1 ≤ t)
    (hdec : ∀ H u v, dec H u v = false → ∀ F : Finset V, #F ≤ f → u ∉ F → v ∉ F →
      (H.deleteVerts F).edist u v ≤ t)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) :
    IsVFTSpanner G (greedyGraph dec L) f t := by
  refine isWeightedVFTSpanner_one_iff.mp (greedyGraph_isWeightedVFTSpanner ht
    (fun i _ hno F hF h1 h2 => ?_) hLG hL)
  rw [wdist_one, ENNReal.coe_one, mul_one, ← ENat.toENNReal_coe, ENat.toENNReal_le]
  exact hdec _ _ _ hno F hF h1 h2

/-- **Correctness of the greedy scheme (unweighted, edge faults).** -/
theorem greedyGraph_isEFTSpanner {G : SimpleGraph V} {L : List (V × V)} {f t : ℕ} (ht : 1 ≤ t)
    (hdec : ∀ H u v, dec H u v = false → ∀ F : Finset (Sym2 V), #F ≤ f →
      (H.deleteEdges F).edist u v ≤ t)
    (hLG : ∀ p ∈ L, G.Adj p.1 p.2) (hL : ∀ u v, G.Adj u v → (u, v) ∈ L ∨ (v, u) ∈ L) :
    IsEFTSpanner G (greedyGraph dec L) f t := by
  refine isWeightedEFTSpanner_one_iff.mp (greedyGraph_isWeightedEFTSpanner ht
    (fun i _ hno F hF _ => ?_) hLG hL)
  rw [wdist_one, ENNReal.coe_one, mul_one, ← ENat.toENNReal_coe, ENat.toENNReal_le]
  exact hdec _ _ _ hno F hF

/-! ### Blocking sets from insertion histories -/

/-- **Blocking sets from an insertion history.** Let `A` be a list of edges in insertion order
(e.g. `greedyEdges dec L`) such that the `i`-th edge `(u, v)` is new, and comes with a set
`X_i ∌ u, v` of at most `D` vertices hitting every `u`–`v` walk of length `≤ t - 1` that uses only
earlier edges. Then `edgeGraph A` has a `t`-blocking set of size `≤ D · |E|`: for a cycle `C` with
`≤ t` edges, let `e` be its edge inserted last; then `C - e` is a short walk of earlier edges
between the endpoints of `e`, so it meets `X_e`. -/
theorem exists_blockingSet_of_insertion {A : List (V × V)} {t D : ℕ}
    (hne : ∀ i (h : i < A.length), A[i].1 ≠ A[i].2)
    (hnew : ∀ i (h : i < A.length), ¬ (edgeGraph (A.take i)).Adj A[i].1 A[i].2)
    (X : ∀ i, i < A.length → Finset V) (hXcard : ∀ i h, #(X i h) ≤ D)
    (hXe : ∀ i h, ∀ x ∈ X i h, x ≠ A[i].1 ∧ x ≠ A[i].2)
    (hhit : ∀ i (h : i < A.length) (p : (edgeGraph (A.take i)).Walk A[i].1 A[i].2),
      p.length + 1 ≤ t →
      (∀ e ∈ p.edges, ∃ j, ∃ hj : j < A.length, j < i ∧ e = s(A[j].1, A[j].2)) →
      ∃ x ∈ p.support, x ∈ X i h) :
    ∃ B : Finset (V × Sym2 V), (edgeGraph A).IsBlockingSet t B ∧
      #B ≤ D * (edgeGraph A).edgeSet.ncard := by
  classical
  set M : List (Sym2 V) := A.map (fun p => s(p.1, p.2)) with hM
  have hMlen : M.length = A.length := by simp [hM]
  have hMget : ∀ i (h : i < M.length), M[i] = s(A[i].1, A[i].2) := by
    intro i h; simp [hM]
  -- no edge is inserted twice
  have hnodup : M.Nodup := by
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro j i hj hi hji heq
    rw [hMlen] at hj hi
    rw [hMget j (by omega), hMget i (by omega)] at heq
    apply hnew i hi
    refine edgeGraph_adj.mpr ⟨hne i hi, A[j], ?_, heq⟩
    have : (A.take i)[j]'(by simp; omega) = A[j] := List.getElem_take
    rw [← this]
    exact List.getElem_mem _
  have hmemM : ∀ e, e ∈ (edgeGraph A).edgeSet ↔ e ∈ M := by
    intro e
    rw [mem_edgeSet_edgeGraph]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, -⟩
      exact List.mem_map_of_mem hp
    · intro he
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      rw [hMget]
      refine ⟨⟨A[i], List.getElem_mem _, rfl⟩, ?_⟩
      simpa using hne i (by omega)
  have hncard : (edgeGraph A).edgeSet.ncard = A.length := by
    have : (edgeGraph A).edgeSet = ↑M.toFinset := by
      ext e; simp [hmemM]
    rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup, hMlen]
  -- the blocking set
  let B : Finset (V × Sym2 V) := univ.biUnion fun i : Fin A.length =>
    (X i i.2).image fun x => (x, s(A[i].1, A[i].2))
  refine ⟨B, ⟨?_, ?_⟩, ?_⟩
  · -- pairs are (vertex ∉ edge, edge)
    intro p hp
    simp only [B, mem_biUnion, mem_univ, true_and, mem_image] at hp
    obtain ⟨i, x, hx, rfl⟩ := hp
    refine ⟨(hmemM _).mpr ?_, ?_⟩
    · exact List.mem_map.mpr ⟨_, List.getElem_mem i.2, rfl⟩
    · obtain ⟨hu, hv⟩ := hXe i i.2 x hx
      simp only [Sym2.mem_iff, not_or]
      exact ⟨hu, hv⟩
  · -- every short cycle is blocked
    intro v c hc hlen
    have hcM : ∀ e ∈ c.edges, e ∈ M := fun e he => (hmemM e).mp (c.edges_subset_edgeSet he)
    have hne' : c.edges.toFinset.Nonempty := by
      cases c with
      | nil => exact absurd hc (by simp [Walk.isCycle_def])
      | cons h q => simp
    obtain ⟨e, he, hmax⟩ := c.edges.toFinset.exists_max_image (fun e => M.idxOf e) hne'
    rw [List.mem_toFinset] at he
    set i := M.idxOf e with hi_def
    have hiM : i < M.length := List.idxOf_lt_length_of_mem (hcM e he)
    have hiA : i < A.length := by omega
    have hMi : M[i] = e := List.getElem_idxOf hiM
    have heA : e = s(A[i].1, A[i].2) := by rw [← hMi, hMget]
    rw [heA] at he
    obtain ⟨p, -, hpe, hps, hpl⟩ := hc.exists_path_of_mem_edges he
    -- all edges of `p` were inserted before `e`
    have hold : ∀ e' ∈ p.edges, ∃ j, ∃ hj : j < A.length, j < i ∧ e' = s(A[j].1, A[j].2) := by
      intro e' he'
      obtain ⟨he'c, he'ne⟩ := hpe e' he'
      have hj : M.idxOf e' < M.length := List.idxOf_lt_length_of_mem (hcM e' he'c)
      have hMj : M[M.idxOf e'] = e' := List.getElem_idxOf hj
      have hle : M.idxOf e' ≤ i := hmax e' (List.mem_toFinset.mpr he'c)
      have hlt : M.idxOf e' < i := by
        refine lt_of_le_of_ne hle fun heq => he'ne ?_
        rw [← hMj, ← heA, ← hMi]
        simp only [heq]
      exact ⟨M.idxOf e', by omega, hlt, by rw [← hMget _ hj, hMj]⟩
    have hpold : ∀ e' ∈ p.edges, e' ∈ (edgeGraph (A.take i)).edgeSet := by
      intro e' he'
      obtain ⟨j, hj, hji, rfl⟩ := hold e' he'
      rw [mem_edgeSet_edgeGraph]
      refine ⟨⟨A[j], ?_, rfl⟩, ?_⟩
      · have : (A.take i)[j]'(by simp; omega) = A[j] := List.getElem_take
        rw [← this]
        exact List.getElem_mem _
      · exact (edgeGraph A).not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he')
    let p' := p.transfer (edgeGraph (A.take i)) hpold
    obtain ⟨x, hxp, hxX⟩ := hhit i hiA p' (by simp only [p', Walk.length_transfer]; omega)
      (fun e' he' => hold e' (by simpa [p', Walk.edges_transfer] using he'))
    have hxs : x ∈ p.support := by simpa [p', Walk.support_transfer] using hxp
    refine ⟨(x, s(A[i].1, A[i].2)), ?_, hps x hxs, he⟩
    simp only [B, mem_biUnion, mem_univ, true_and, mem_image]
    exact ⟨⟨i, hiA⟩, x, hxX, rfl⟩
  · -- size
    rw [hncard]
    calc #B ≤ ∑ i : Fin A.length, #((X i i.2).image fun x => (x, s(A[i].1, A[i].2))) :=
          card_biUnion_le
      _ ≤ ∑ _i : Fin A.length, D := sum_le_sum fun i _ => card_image_le.trans (hXcard i i.2)
      _ = D * A.length := by simp [mul_comm]

/-! ### Inputs -/

/-- Every finite graph admits an edge list as required by the greedy schemes: entries are edges,
every edge occurs, and the list is sorted by weight. -/
theorem exists_sorted_edgeList [Finite V] (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) :
    ∃ L : List (V × V), (∀ p ∈ L, G.Adj p.1 p.2) ∧ (∀ u v, G.Adj u v → (u, v) ∈ L) ∧
      L.Pairwise fun a b => w s(a.1, a.2) ≤ w s(b.1, b.2) := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨L, -, hmem, hsort⟩ :=
    (univ.filter fun p : V × V => G.Adj p.1 p.2).exists_list_nodup_pairwise_le
      fun p => w s(p.1, p.2)
  exact ⟨L, fun p hp => by simpa using (hmem p).1 hp,
    fun u v huv => (hmem _).2 (by simpa using huv), hsort⟩

end SimpleGraph
