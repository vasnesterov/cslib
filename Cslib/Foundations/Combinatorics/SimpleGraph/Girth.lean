/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Short cycles, girth and the Moore bound

* `G.NoShortCycles L` — every cycle of `G` has length `> L` (i.e. girth `> L`);
  `noShortCycles_iff_lt_egirth` relates it to Mathlib's `egirth`.
* `NoShortCycles.anti` — inherited by subgraphs.
* `NoShortCycles.path_eq` — if `G` has no cycle of length `≤ 2k`, two `u`–`v` paths of length `≤ k`
  coincide.
* `NoShortCycles.pow_lt_card` — core counting step: if every vertex of `S ∋ v` has degree `> d`
  and all edges lie inside `S`, then `d ^ k < |S|` (paths of length `k` from `v` have distinct
  ends).
* **Moore bound** `NoShortCycles.ncard_edgeSet_le`: if `G` has girth `> 2k` (`k ≥ 1`), all edges
  lie inside `S` and `|S| ≤ d^k`, then `|E(G)| ≤ d · |S|`; real form
  `NoShortCycles.ncard_edgeSet_le_rpow`: `|E(G)| ≤ n^{1 + 1/k} + n`, a corollary of the form
  `NoShortCycles.ncard_edgeSet_le_card_rpow` relative to a vertex set `S` containing all edges.
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V}

/-- `G` has no cycle of length at most `L`, i.e. its girth is larger than `L`. -/
def NoShortCycles (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∀ v (c : G.Walk v v), c.IsCycle → L < c.length

lemma noShortCycles_iff_lt_egirth {L : ℕ} : G.NoShortCycles L ↔ (L : ℕ∞) < G.egirth := by
  rw [← ENat.add_one_le_iff (ENat.natCast_ne_top L), le_egirth]
  refine forall_congr' fun a ↦ forall_congr' fun c ↦ imp_congr_right fun _ ↦ ?_
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_le, Nat.add_one_le_iff]

lemma NoShortCycles.anti {L : ℕ} (hGH : G ≤ H) (h : H.NoShortCycles L) : G.NoShortCycles L :=
  fun v c hc ↦ by simpa using h v (c.mapLe hGH) (hc.mapLe hGH)

/-- In a graph of girth `> 2k`, two `u`–`v` paths of length `≤ k` are equal. -/
theorem NoShortCycles.path_eq {k : ℕ} (h : G.NoShortCycles (2 * k)) {u v : V}
    {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath) (hpk : p.length ≤ k) (hqk : q.length ≤ k) :
    p = q := by
  classical
  by_contra hne
  -- the graph formed by the edges of `p` and `q`
  set s : Finset (Sym2 V) := p.edges.toFinset ∪ q.edges.toFinset
  set K : SimpleGraph V := fromEdgeSet (s : Set (Sym2 V))
  have hKG : K ≤ G := by
    rw [fromEdgeSet_le]
    rintro e ⟨he, -⟩
    rcases Finset.mem_union.mp he with he | he
    · exact p.edges_subset_edgeSet (List.mem_toFinset.mp he)
    · exact q.edges_subset_edgeSet (List.mem_toFinset.mp he)
  have hpK : ∀ e ∈ p.edges, e ∈ K.edgeSet := fun e he ↦ by
    rw [edgeSet_fromEdgeSet]
    exact ⟨by simp [s, he],
      by simpa using G.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he)⟩
  have hqK : ∀ e ∈ q.edges, e ∈ K.edgeSet := fun e he ↦ by
    rw [edgeSet_fromEdgeSet]
    exact ⟨by simp [s, he],
      by simpa using G.not_isDiag_of_mem_edgeSet (q.edges_subset_edgeSet he)⟩
  have hK : ¬ K.IsAcyclic := by
    intro hK
    have := (isAcyclic_iff_subsingleton_path.mp hK u v).elim
      ⟨p.transfer K hpK, hp.transfer hpK⟩ ⟨q.transfer K hqK, hq.transfer hqK⟩
    apply hne
    have h' := congrArg (fun r : K.Path u v ↦ (r : K.Walk u v).transfer G
      (fun e he ↦ edgeSet_mono hKG ((r : K.Walk u v).edges_subset_edgeSet he))) this
    simpa [Walk.transfer_transfer, Walk.transfer_self] using h'
  simp only [IsAcyclic, not_forall, not_not] at hK
  obtain ⟨w, c, hc⟩ := hK
  have hlen : c.length ≤ 2 * k := by
    have hsub : c.edges.toFinset ⊆ s := fun e he ↦ by
      have := c.edges_subset_edgeSet (List.mem_toFinset.mp he)
      rw [edgeSet_fromEdgeSet] at this
      exact this.1
    calc c.length = c.edges.toFinset.card := by
          rw [List.toFinset_card_of_nodup hc.edges_nodup, Walk.length_edges]
      _ ≤ s.card := Finset.card_le_card hsub
      _ ≤ p.edges.toFinset.card + q.edges.toFinset.card := Finset.card_union_le _ _
      _ ≤ p.edges.length + q.edges.length :=
          Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
      _ ≤ 2 * k := by simp only [Walk.length_edges]; omega
  have := h w (c.mapLe hKG) (hc.mapLe hKG)
  simp only [Walk.length_mapLe] at this
  omega

/-- In a graph of girth `> 2k` (`k ≥ 1`), the endpoint `x` of a path `p` of length `≤ k` has at most
one neighbour on `p`: any such neighbour `y` satisfies `p = (p.takeUntil y).concat (y ~ x)`. -/
lemma NoShortCycles.eq_of_adj_mem_support {k : ℕ} (hk : 1 ≤ k) (h : G.NoShortCycles (2 * k))
    {v x y y' : V} {p : G.Walk v x} (hp : p.IsPath) (hpk : p.length ≤ k)
    (hy : y ∈ p.support) (hy' : y' ∈ p.support) (hyx : G.Adj y x) (hy'x : G.Adj y' x) :
    y = y' := by
  classical
  have key : ∀ z (hz : z ∈ p.support) (hzx : G.Adj z x), p = (p.takeUntil z hz).concat hzx := by
    intro z hz hzx
    have hd := h.path_eq (hp.dropUntil hz) (q := Walk.cons hzx Walk.nil) (by simp [hzx.ne])
      ((p.length_dropUntil_le_length hz).trans hpk) (by simpa using hk)
    conv_lhs => rw [← p.take_spec hz, hd]
    rw [Walk.concat_eq_append]
  obtain ⟨rfl, -⟩ := Walk.concat_inj ((key y hy hyx).symm.trans (key y' hy' hy'x))
  rfl

/-- The vertices reachable from `v` by a path of length exactly `i`. -/
private noncomputable def pathLayer [Fintype V] (G : SimpleGraph V) (v : V) (i : ℕ) : Finset V := by
  classical
  exact univ.filter fun x ↦ ∃ p : G.Walk v x, p.IsPath ∧ p.length = i

private lemma mem_pathLayer [Fintype V] {v x : V} {i : ℕ} :
    x ∈ pathLayer G v i ↔ ∃ p : G.Walk v x, p.IsPath ∧ p.length = i := by
  classical
  simp [pathLayer]

/-- **Core of the Moore bound.** If `G` has girth `> 2k` (`k ≥ 1`), all edges lie inside `S`, and
every vertex of `S` has degree `> d`, then `|S| > d ^ k` (as soon as `S` is nonempty): the paths of
length `i ≤ k` from a fixed vertex end at pairwise distinct vertices, and there are at least `d ^ k`
of them for `i = k`. -/
theorem NoShortCycles.pow_lt_card [Fintype V] [DecidableRel G.Adj] {k d : ℕ} (hk : 1 ≤ k)
    (h : G.NoShortCycles (2 * k)) (S : Finset V) (hS : ∀ u v, G.Adj u v → u ∈ S)
    (hdeg : ∀ x ∈ S, d < G.degree x) {v : V} (hv : v ∈ S) : d ^ k < #S := by
  classical
  -- every endpoint of a walk from `v` lies in `S`
  have hmemS : ∀ {x} (p : G.Walk v x), x ∈ S := by
    intro x p
    by_cases hxv : x = v
    · exact hxv ▸ hv
    · have hnil : ¬ p.Nil := Walk.not_nil_of_ne (Ne.symm hxv)
      exact hS _ _ (Walk.adj_penultimate hnil).symm
  have hstep : ∀ i < k, #(pathLayer G v i) * d ≤ #(pathLayer G v (i + 1)) * 1 := by
    intro i hi
    let r : V → V → Prop := fun x y ↦
      G.Adj x y ∧ ∃ p : G.Walk v x, p.IsPath ∧ p.length = i ∧ y ∉ p.support
    apply Finset.card_mul_le_card_mul r
    · intro x hx
      obtain ⟨p, hp, hpl⟩ := mem_pathLayer.mp hx
      have hTsub : (G.neighborFinset x).filter (· ∉ p.support) ⊆
          (pathLayer G v (i + 1)).bipartiteAbove r x := by
        intro y hyT
        simp only [Finset.mem_filter, mem_neighborFinset] at hyT
        simp only [Finset.mem_bipartiteAbove, mem_pathLayer]
        exact ⟨⟨p.concat hyT.1, hp.concat hyT.2 hyT.1, by simp [hpl]⟩,
          hyT.1, p, hp, hpl, hyT.2⟩
      have hle : #((G.neighborFinset x).filter (· ∈ p.support)) ≤ 1 := by
        refine Finset.card_le_one.mpr fun a ha b hb ↦ ?_
        simp only [Finset.mem_filter, mem_neighborFinset] at ha hb
        exact h.eq_of_adj_mem_support hk hp (by omega) ha.2 hb.2 ha.1.symm hb.1.symm
      have hcard := Finset.card_filter_add_card_filter_not (s := G.neighborFinset x)
        (fun y ↦ y ∈ p.support)
      rw [card_neighborFinset_eq_degree] at hcard
      have := hdeg x (hmemS p)
      have := Finset.card_le_card hTsub
      omega
    · intro y hy
      refine Finset.card_le_one.mpr fun a ha b hb ↦ ?_
      simp only [Finset.mem_bipartiteBelow, r] at ha hb
      obtain ⟨-, hay, p, hp, hpl, hyp⟩ := ha
      obtain ⟨-, hby, q, hq, hql, hyq⟩ := hb
      have := h.path_eq (hp.concat hyp hay) (hq.concat hyq hby) (by simp; omega) (by simp; omega)
      obtain ⟨rfl, -⟩ := Walk.concat_inj this
      rfl
  have hpow : ∀ i ≤ k, d ^ i ≤ #(pathLayer G v i) := by
    intro i hi
    induction i with
    | zero =>
      simpa using Finset.card_pos.mpr ⟨v, mem_pathLayer.mpr ⟨Walk.nil, by simp, rfl⟩⟩
    | succ i ih =>
      have := hstep i (by omega)
      calc d ^ (i + 1) = d ^ i * d := pow_succ d i
        _ ≤ #(pathLayer G v i) * d := Nat.mul_le_mul_right d (ih (by omega))
        _ ≤ #(pathLayer G v (i + 1)) := by simpa using this
  have hsub : pathLayer G v k ⊆ S.erase v := by
    intro x hx
    obtain ⟨p, hp, hpl⟩ := mem_pathLayer.mp hx
    refine Finset.mem_erase.mpr ⟨?_, hmemS p⟩
    rintro rfl
    rw [Walk.isPath_iff_nil.mp hp |>.eq_nil] at hpl
    simp at hpl
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hv] at this
  have := hpow k le_rfl
  have : 0 < #S := Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-- **Moore bound** (natural-number form). If `G` has girth `> 2k` with `k ≥ 1`, every edge of `G`
has its endpoints in `S`, and `|S| ≤ d ^ k`, then `G` has at most `d · |S|` edges. -/
theorem NoShortCycles.ncard_edgeSet_le [Finite V] {k d : ℕ} (hk : 1 ≤ k)
    (h : G.NoShortCycles (2 * k)) (S : Finset V) (hS : ∀ u v, G.Adj u v → u ∈ S)
    (hd : #S ≤ d ^ k) : G.edgeSet.ncard ≤ d * #S := by
  classical
  have := Fintype.ofFinite V
  induction S using Finset.strongInduction generalizing G with
  | H S ih =>
  by_cases hx : ∃ x ∈ S, G.degree x ≤ d
  · -- delete a vertex of small degree and induct
    obtain ⟨x, hxS, hxd⟩ := hx
    have h1 := ih (S.erase x) (Finset.erase_ssubset hxS) (G := G.deleteIncidenceSet x)
      (h.anti (G.deleteIncidenceSet_le x))
      (fun u w huw ↦ by
        rw [deleteIncidenceSet_adj] at huw
        exact Finset.mem_erase.mpr ⟨huw.2.1, hS _ _ huw.1⟩)
      ((Finset.card_erase_le).trans hd)
    have h2 : G.edgeSet.ncard = (G.deleteIncidenceSet x).edgeSet.ncard + G.degree x := by
      rw [edgeSet_deleteIncidenceSet, Set.ncard_sdiff (G.incidenceSet_subset x),
        ← card_incidenceSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
        Nat.sub_add_cancel (Set.ncard_le_ncard (G.incidenceSet_subset x))]
    have h3 := Finset.card_erase_add_one hxS
    rw [h2, ← h3, Nat.mul_add_one]
    omega
  · push Not at hx
    rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · have : G = ⊥ := by
        ext u w
        simpa using fun huw ↦ Finset.notMem_empty u (hS u w huw)
      simp [this]
    · exact absurd hd (not_le.mpr (h.pow_lt_card hk S hS hx hv))

/-- **Moore bound relative to a vertex set.** If all edges of `G` have their endpoints in `S` and
`G` has girth `> 2k`, then `|E(G)| ≤ |S|^{1+1/k} + |S|`. This is the form needed when the graph
lives on a large vertex type but only uses the vertices of `S` (e.g. a spanner of an induced
subgraph `G[S]`). -/
theorem NoShortCycles.ncard_edgeSet_le_card_rpow [Finite V] {k : ℕ} (hk : 1 ≤ k)
    (h : G.NoShortCycles (2 * k)) (S : Finset V) (hS : ∀ u v, G.Adj u v → u ∈ S) :
    (G.edgeSet.ncard : ℝ) ≤ (#S : ℝ) ^ (1 + 1 / (k : ℝ)) + #S := by
  set s := #S
  have hx : (0 : ℝ) ≤ (s : ℝ) ^ (1 / (k : ℝ)) := by positivity
  set d := ⌈(s : ℝ) ^ (1 / (k : ℝ))⌉₊
  have hd : #S ≤ d ^ k := by
    have : (s : ℝ) ≤ (d : ℝ) ^ k := by
      calc (s : ℝ) = ((s : ℝ) ^ ((k : ℝ)⁻¹)) ^ k :=
            (Real.rpow_inv_natCast_pow (Nat.cast_nonneg s) (by omega)).symm
        _ ≤ (d : ℝ) ^ k := by
            rw [← one_div]
            exact pow_le_pow_left₀ hx (Nat.le_ceil _) k
    exact_mod_cast this
  have hE := h.ncard_edgeSet_le hk S hS hd
  calc (G.edgeSet.ncard : ℝ) ≤ d * s := by exact_mod_cast hE
    _ ≤ ((s : ℝ) ^ (1 / (k : ℝ)) + 1) * s :=
        mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hx).le (Nat.cast_nonneg _)
    _ = (s : ℝ) ^ (1 + 1 / (k : ℝ)) + s := by
        rw [Real.rpow_add' (Nat.cast_nonneg _) (by positivity), Real.rpow_one]
        ring

/-- **Moore bound** (real form): a graph on `n` vertices with girth `> 2k` has at most
`n ^ (1 + 1/k) + n` edges. -/
theorem NoShortCycles.ncard_edgeSet_le_rpow [Fintype V] {k : ℕ} (hk : 1 ≤ k)
    (h : G.NoShortCycles (2 * k)) :
    (G.edgeSet.ncard : ℝ) ≤ (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) + Fintype.card V := by
  simpa using h.ncard_edgeSet_le_card_rpow hk univ fun _ _ _ ↦ mem_univ _

end SimpleGraph
