/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Foundations.Combinatorics.SimpleGraph.Spanner
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Weighted distances and weighted (fault-tolerant) spanners

Edge weights are a function `w : Sym2 V → ℝ≥0` (only its values on edges matter).

* `Walk.wlength w p` — the total weight of a walk (in `ℝ≥0∞`).
* `G.wdist w u v` — the weighted distance: infimum of `wlength` over all `u`–`v` walks
  (`⊤` if `u, v` are disconnected).
* `wdist_le_mul_of_adj` — local criterion: if `d_H(x, y) ≤ t · w(xy)` for every edge `xy` of `G`,
  then `d_H ≤ t · d_G`.
* `IsWeightedVFTSpanner` — Definition 1 of Dinitz–Robelle for weighted graphs (vertex faults);
  `isWeightedVFTSpanner_of_adj` is the "if" direction of their Lemma 3 (in the stronger-hypothesis
  form that checks all edges, not only edges that are shortest paths).

## Weighted distances

* `wdist_one`: with unit weights the weighted distance is the unweighted one,
  `G.wdist (fun _ => 1) u v = G.edist u v` (via the coercion `ℕ∞ → ℝ≥0∞`).
* `wdist_lt_top_iff`: `wdist` is finite exactly between connected vertices; `wdist_self`.
* `exists_isPath_wlength_eq`: on a finite graph, `wdist` is attained by a path.
* `wdist_smul`: scaling the weights by `t ≠ 0` scales distances by `t`.
* `wdist_le_wdist_of_forall_adj`: comparison of two weighted graphs edge by edge; this is the
  local criterion for spanners in its most general form (`wdist_le_mul_of_adj` is the case of a
  natural stretch).
* `wdistS`: `wdist` as a function of an unordered pair.

## Spanners with a real stretch

* `IsWSpanner G H w t`: `H ≤ G` and `d_H(u, v) ≤ t · d_G(u, v)` for a real stretch `t : ℝ≥0`;
  `isWSpanner_of_adj` (local criterion).
* Bridges: natural stretches are the casts `(t : ℝ≥0)` (`isWSpanner_natCast_iff`); unit weights
  give the unweighted notions (`isWeightedVFTSpanner_one_iff`, `isWeightedEFTSpanner_one_iff`).
-/

@[expose] public section

open Finset
open scoped ENNReal NNReal

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} (w : Sym2 V → ℝ≥0)

/-- Total weight of a walk. -/
noncomputable def Walk.wlength {u v : V} (p : G.Walk u v) : ℝ≥0∞ :=
  (p.edges.map fun e => (w e : ℝ≥0∞)).sum

@[simp] lemma Walk.wlength_nil {u : V} : (Walk.nil : G.Walk u u).wlength w = 0 := by
  simp [Walk.wlength]

@[simp] lemma Walk.wlength_cons {u v x : V} (h : G.Adj u v) (p : G.Walk v x) :
    (Walk.cons h p).wlength w = w s(u, v) + p.wlength w := by
  simp [Walk.wlength]

lemma Walk.wlength_eq_of_edges_eq {u v : V} {G' : SimpleGraph V} (p : G.Walk u v)
    (q : G'.Walk u v) (h : p.edges = q.edges) : p.wlength w = q.wlength w := by
  simp [Walk.wlength, h]

@[simp] lemma Walk.wlength_mapLe {u v : V} (hGH : G ≤ H) (p : G.Walk u v) :
    (p.mapLe hGH).wlength w = p.wlength w := by
  simp [Walk.wlength]

@[simp] lemma Walk.wlength_transfer {u v : V} (p : G.Walk u v) (hp) :
    (p.transfer H hp).wlength w = p.wlength w := by
  simp [Walk.wlength, Walk.edges_transfer]

@[simp] lemma Walk.wlength_reverse {u v : V} (p : G.Walk u v) :
    p.reverse.wlength w = p.wlength w := by
  simp [Walk.wlength, Walk.edges_reverse, List.map_reverse, List.sum_reverse]

/-- If every edge of `p` weighs at most `c`, then `wlength p ≤ |p| · c`. -/
lemma Walk.wlength_le_length_mul {u v : V} (p : G.Walk u v) {c : ℝ≥0∞}
    (h : ∀ e ∈ p.edges, (w e : ℝ≥0∞) ≤ c) : p.wlength w ≤ p.length * c := by
  induction p with
  | nil => simp
  | @cons a b x hadj q ih =>
    rw [Walk.wlength_cons, Walk.length_cons]
    have h1 := h s(a, b) (by simp)
    have h2 := ih fun e he => h e (by rw [Walk.edges_cons]; exact List.mem_cons_of_mem _ he)
    push_cast
    calc (w _ : ℝ≥0∞) + q.wlength w ≤ c + q.length * c := add_le_add h1 h2
      _ = (q.length + 1) * c := by ring

/-- The weighted distance (`⊤` if there is no walk). -/
noncomputable def wdist (G : SimpleGraph V) (u v : V) : ℝ≥0∞ :=
  ⨅ p : G.Walk u v, p.wlength w

variable {w}

lemma wdist_le {u v : V} (p : G.Walk u v) : G.wdist w u v ≤ p.wlength w := iInf_le _ p

lemma wdist_le_of_adj {u v : V} (h : G.Adj u v) : G.wdist w u v ≤ w s(u, v) := by
  simpa using wdist_le (w := w) (Walk.cons h (Walk.nil : G.Walk v v))

lemma wdist_triangle {u v x : V} : G.wdist w u x ≤ G.wdist w u v + G.wdist w v x := by
  refine ENNReal.le_iInf_add_iInf fun p q => ?_
  refine (wdist_le (p.append q)).trans (le_of_eq ?_)
  simp [Walk.wlength, Walk.edges_append]

lemma wdist_anti {u v : V} (h : G ≤ H) : H.wdist w u v ≤ G.wdist w u v :=
  le_iInf fun p => (wdist_le (p.mapLe h)).trans (by simp)

lemma wdist_comm {u v : V} : G.wdist w u v = G.wdist w v u :=
  le_antisymm (le_iInf fun p => (wdist_le p.reverse).trans (by simp))
    (le_iInf fun p => (wdist_le p.reverse).trans (by simp))

/-! ### Walk weights -/

section

variable {u v : V}

namespace Walk

/-- The weight of a walk is finite. -/
theorem wlength_lt_top (p : G.Walk u v) : p.wlength w < ⊤ := by
  induction p with
  | nil => simp
  | cons h q ih => rw [wlength_cons]; exact ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top, ih⟩

/-- Every edge of a walk weighs at most the walk. -/
theorem le_wlength_of_mem_edges (p : G.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) :
    (w e : ℝ≥0∞) ≤ p.wlength w :=
  List.single_le_sum (fun _ _ => zero_le) _ (List.mem_map_of_mem he)

/-- With unit weights, the weight of a walk is its length. -/
@[simp] theorem wlength_one (p : G.Walk u v) : p.wlength (fun _ => 1) = p.length := by
  induction p with
  | nil => simp
  | cons h q ih => rw [wlength_cons, ih, length_cons]; push_cast; ring

/-- Scaling the weights scales the weight of a walk. -/
theorem wlength_smul (t : ℝ≥0) (p : G.Walk u v) : p.wlength (t • w) = t * p.wlength w := by
  simp only [wlength, Pi.smul_apply, smul_eq_mul, ENNReal.coe_mul, List.sum_map_mul_left]

/-- Bypassing a walk does not increase its weight (weights are nonnegative). -/
theorem wlength_bypass_le [DecidableEq V] (p : G.Walk u v) : p.bypass.wlength w ≤ p.wlength w := by
  obtain ⟨l, hl, hsub⟩ := List.subperm_of_subset p.bypass_isPath.isTrail.edges_nodup
    p.edges_bypass_subset_edges
  rw [wlength, wlength, ← (hl.map _).sum_eq]
  exact (hsub.map _).sum_le_sum fun _ _ => zero_le

end Walk

/-! ### Weighted distances -/

/-- The weighted distance from a vertex to itself is `0`. -/
@[simp] theorem wdist_self : G.wdist w u u = 0 :=
  le_antisymm ((wdist_le (Walk.nil : G.Walk u u)).trans (by simp)) zero_le

/-- Disconnected vertices are at weighted distance `⊤`. -/
theorem wdist_eq_top_of_not_reachable (h : ¬ G.Reachable u v) : G.wdist w u v = ⊤ := by
  have : IsEmpty (G.Walk u v) := ⟨fun p => h ⟨p⟩⟩
  simp [wdist]

/-- Connected vertices are at finite weighted distance. -/
theorem wdist_lt_top_of_reachable (h : G.Reachable u v) : G.wdist w u v < ⊤ :=
  (wdist_le h.some).trans_lt h.some.wlength_lt_top

/-- The weighted distance is finite exactly between connected vertices. -/
theorem wdist_lt_top_iff : G.wdist w u v < ⊤ ↔ G.Reachable u v :=
  ⟨fun h => by_contra fun hr => (wdist_eq_top_of_not_reachable hr ▸ h).ne rfl,
    wdist_lt_top_of_reachable⟩

/-- Vertices at finite weighted distance are connected. -/
theorem reachable_of_wdist_lt_top (h : G.wdist w u v < ⊤) : G.Reachable u v :=
  wdist_lt_top_iff.mp h

/-- **Unit weights.** With all weights `1`, the weighted distance is the unweighted distance. -/
theorem wdist_one : G.wdist (fun _ => 1) u v = G.edist u v := by
  by_cases hr : G.Reachable u v
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    refine le_antisymm ((wdist_le p).trans (by simp [← hp, ENat.toENNReal_coe])) ?_
    refine le_iInf fun q => ?_
    rw [Walk.wlength_one, ← ENat.toENNReal_coe, ENat.toENNReal_le]
    exact edist_le q
  · rw [wdist_eq_top_of_not_reachable hr, edist_eq_top_of_not_reachable hr, ENat.toENNReal_top]

/-- On a finite graph, the weighted distance between connected vertices is the weight of a path. -/
theorem exists_isPath_wlength_eq [Finite V] (h : G.Reachable u v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.wlength w = G.wdist w u v := by
  classical
  have := Fintype.ofFinite V
  set S : Set (G.Walk u v) := {p | p.IsPath ∧ p.length < Fintype.card V}
  have hne : S.Nonempty := ⟨h.some.bypass, h.some.bypass_isPath, h.some.bypass_isPath.length_lt⟩
  obtain ⟨p, hpS, hpmin⟩ := Set.exists_min_image S (fun p => p.wlength w) (Set.toFinite S) hne
  refine ⟨p, hpS.1, le_antisymm (le_iInf fun q => ?_) (wdist_le p)⟩
  exact (hpmin q.bypass ⟨q.bypass_isPath, q.bypass_isPath.length_lt⟩).trans q.wlength_bypass_le

/-- **Scaling.** Multiplying all weights by `t ≠ 0` multiplies all distances by `t`. -/
theorem wdist_smul {t : ℝ≥0} (ht : t ≠ 0) : G.wdist (t • w) u v = t * G.wdist w u v := by
  simp only [wdist, Walk.wlength_smul]
  rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast ht) ENNReal.coe_ne_top]

/-- **Comparison along a walk.** If every edge `ab` of a walk `p` (of any graph) satisfies
`d_H^{w₁}(a, b) ≤ w₂(ab)`, then `d_H^{w₁}(u, v) ≤ w₂(p)`. -/
theorem wdist_le_wlength_of_forall_adj {K : SimpleGraph V} {w₁ w₂ : Sym2 V → ℝ≥0}
    (p : K.Walk u v) (h : ∀ a b, s(a, b) ∈ p.edges → H.wdist w₁ a b ≤ w₂ s(a, b)) :
    H.wdist w₁ u v ≤ p.wlength w₂ := by
  induction p with
  | nil => simp
  | @cons a b c hab q ih =>
    rw [Walk.wlength_cons]
    calc H.wdist w₁ a c ≤ H.wdist w₁ a b + H.wdist w₁ b c := wdist_triangle
      _ ≤ w₂ s(a, b) + q.wlength w₂ :=
        add_le_add (h a b (by simp)) (ih fun x y hxy => h x y (by simp [hxy]))

/-- **Local comparison of weighted graphs.** If every edge `ab` of `(K, w₂)` satisfies
`d_H^{w₁}(a, b) ≤ w₂(ab)`, then `d_H^{w₁} ≤ d_K^{w₂}` everywhere. -/
theorem wdist_le_wdist_of_forall_adj {K : SimpleGraph V} {w₁ w₂ : Sym2 V → ℝ≥0}
    (h : ∀ a b, K.Adj a b → H.wdist w₁ a b ≤ w₂ s(a, b)) : H.wdist w₁ u v ≤ K.wdist w₂ u v :=
  le_iInf fun p => wdist_le_wlength_of_forall_adj p fun a b hab => h a b (p.adj_of_mem_edges hab)

/-- The weighted distance as a function of an unordered pair. -/
noncomputable def wdistS (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) (e : Sym2 V) : ℝ≥0∞ :=
  Sym2.lift ⟨fun u v => G.wdist w u v, fun _ _ => wdist_comm⟩ e

/-- `wdistS` on `s(u, v)` is `wdist` between `u` and `v`. -/
@[simp] theorem wdistS_mk (u v : V) : G.wdistS w s(u, v) = G.wdist w u v := rfl

end

/-! ### Stretch -/

/-- Stretch along a walk: if every edge `ab` of a `G`-walk `p` has `d_H(a, b) ≤ t · w(ab)`, then
`d_H(u, v) ≤ t · w(p)`. -/
lemma wdist_le_mul_wlength {t : ℝ≥0∞} {u v : V} (p : G.Walk u v)
    (h : ∀ a b, G.Adj a b → s(a, b) ∈ p.edges → H.wdist w a b ≤ t * w s(a, b)) :
    H.wdist w u v ≤ t * p.wlength w := by
  induction p with
  | nil => simp [wdist, iInf_le_of_le Walk.nil]
  | @cons x y z hxy q ih =>
    calc H.wdist w x z ≤ H.wdist w x y + H.wdist w y z := wdist_triangle
      _ ≤ t * w s(x, y) + t * q.wlength w :=
        add_le_add (h _ _ hxy (by simp)) (ih fun a b hab he => h a b hab (by simp [he]))
      _ = t * (Walk.cons hxy q).wlength w := by rw [Walk.wlength_cons, mul_add]

/-- **Local criterion for weighted stretch.** -/
theorem wdist_le_mul_of_adj {t : ℕ} (ht : 1 ≤ t)
    (h : ∀ x y, G.Adj x y → H.wdist w x y ≤ t * w s(x, y)) (u v : V) :
    H.wdist w u v ≤ t * G.wdist w u v := by
  rw [← ENNReal.coe_natCast, ← wdist_smul (by exact_mod_cast (by omega : t ≠ 0))]
  exact wdist_le_wdist_of_forall_adj fun a b hab => by simpa using h a b hab

/-- **Tight edges suffice.** On a finite graph, if every edge `xy` of `G` that is a shortest path
(`d_G(x, y) = w(xy)`) has `d_H(x, y) ≤ t · w(xy)`, then every edge does. (By strong induction on the
number of lighter edges: a non-tight edge is bypassed by a strictly lighter walk, all of whose edges
are strictly lighter.) -/
theorem wdist_le_mul_of_tight [Finite V] {t : ℝ≥0∞}
    (h : ∀ x y, G.Adj x y → G.wdist w x y = w s(x, y) → H.wdist w x y ≤ t * w s(x, y)) :
    ∀ x y, G.Adj x y → H.wdist w x y ≤ t * w s(x, y) := by
  classical
  have := Fintype.ofFinite V
  suffices ∀ n x y, G.Adj x y → #(G.edgeFinset.filter fun e => w e < w s(x, y)) ≤ n →
      H.wdist w x y ≤ t * w s(x, y) from fun x y hxy => this _ x y hxy le_rfl
  intro n
  induction n with
  | zero =>
    intro x y hxy hn
    rw [Nat.le_zero, Finset.card_eq_zero] at hn
    by_cases htight : G.wdist w x y = w s(x, y)
    · exact h x y hxy htight
    exfalso
    have hlt : G.wdist w x y < w s(x, y) := lt_of_le_of_ne (wdist_le_of_adj hxy) htight
    obtain ⟨p, hp⟩ := iInf_lt_iff.mp hlt
    -- `p` has an edge (it joins distinct vertices), which is strictly lighter than `xy`
    cases p with
    | nil => exact hxy.ne rfl
    | @cons _ b _ hab q =>
      have : s(x, b) ∈ G.edgeFinset.filter fun e => w e < w s(x, y) := by
        refine Finset.mem_filter.mpr ⟨(mem_edgeFinset).mpr hab, ?_⟩
        have : (w s(x, b) : ℝ≥0∞) ≤ (Walk.cons hab q).wlength w := by simp
        exact_mod_cast this.trans_lt hp
      simp [hn] at this
  | succ n ih =>
    intro x y hxy hn
    by_cases htight : G.wdist w x y = w s(x, y)
    · exact h x y hxy htight
    have hlt : G.wdist w x y < w s(x, y) := lt_of_le_of_ne (wdist_le_of_adj hxy) htight
    obtain ⟨p, hp⟩ := iInf_lt_iff.mp hlt
    have hedge : ∀ e ∈ p.edges, w e < w s(x, y) := by
      intro e he
      have : (w e : ℝ≥0∞) ≤ p.wlength w := by
        unfold Walk.wlength
        exact List.single_le_sum (fun _ _ => zero_le) _ (List.mem_map_of_mem he)
      exact_mod_cast this.trans_lt hp
    calc H.wdist w x y ≤ t * p.wlength w := by
          refine wdist_le_mul_wlength p fun a b hab he => ih a b hab ?_
          have hsub : (G.edgeFinset.filter fun e => w e < w s(a, b)) ⊂
              G.edgeFinset.filter fun e => w e < w s(x, y) := by
            refine Finset.ssubset_iff_of_subset (fun e he1 => ?_) |>.mpr ⟨s(a, b), ?_, ?_⟩
            · rw [Finset.mem_filter] at he1 ⊢
              exact ⟨he1.1, he1.2.trans (hedge _ he)⟩
            · exact Finset.mem_filter.mpr ⟨(mem_edgeFinset).mpr hab, hedge _ he⟩
            · simp
          have := Finset.card_lt_card hsub
          omega
      _ ≤ t * w s(x, y) := by gcongr

/-- `H` is an `f`-vertex-fault-tolerant `t`-spanner of the weighted graph `(G, w)`
(Definition 1 of Dinitz–Robelle). -/
def IsWeightedVFTSpanner (G H : SimpleGraph V) (w : Sym2 V → ℝ≥0) (f t : ℕ) : Prop :=
  H ≤ G ∧ ∀ F : Finset V, #F ≤ f → ∀ u v, u ∉ F → v ∉ F →
    (H.deleteVerts F).wdist w u v ≤ t * (G.deleteVerts F).wdist w u v

/-- `H` is an `f`-edge-fault-tolerant `t`-spanner of the weighted graph `(G, w)`. -/
def IsWeightedEFTSpanner (G H : SimpleGraph V) (w : Sym2 V → ℝ≥0) (f t : ℕ) : Prop :=
  H ≤ G ∧ ∀ F : Finset (Sym2 V), #F ≤ f → ∀ u v,
    (H.deleteEdges F).wdist w u v ≤ t * (G.deleteEdges F).wdist w u v

/-- **Lemma 3 of Dinitz–Robelle, "if" direction (checking all edges).** If for every fault set `F`
with `|F| ≤ f` and every edge `uv` of `G \ F`, `d_{H \ F}(u, v) ≤ t · w(uv)`, then `H` is an
`f`-VFT `t`-spanner. -/
theorem isWeightedVFTSpanner_of_adj {f t : ℕ} (ht : 1 ≤ t) (hHG : H ≤ G)
    (h : ∀ F : Finset V, #F ≤ f → ∀ u v, G.Adj u v → u ∉ F → v ∉ F →
      (H.deleteVerts F).wdist w u v ≤ t * w s(u, v)) :
    IsWeightedVFTSpanner G H w f t :=
  ⟨hHG, fun F hF _ _ _ _ => wdist_le_mul_of_adj ht
    (fun x y (hxy : (G.deleteVerts F).Adj x y) => h F hF x y hxy.1 hxy.2.1 hxy.2.2) _ _⟩

/-- Edge-fault analogue of `isWeightedVFTSpanner_of_adj`. -/
theorem isWeightedEFTSpanner_of_adj {f t : ℕ} (ht : 1 ≤ t) (hHG : H ≤ G)
    (h : ∀ F : Finset (Sym2 V), #F ≤ f → ∀ u v, G.Adj u v → s(u, v) ∉ F →
      (H.deleteEdges F).wdist w u v ≤ t * w s(u, v)) :
    IsWeightedEFTSpanner G H w f t :=
  ⟨hHG, fun F hF _ _ => wdist_le_mul_of_adj ht
    (fun x y hxy => by
      rw [deleteEdges_adj] at hxy
      exact h F hF x y hxy.1 (by simpa using hxy.2)) _ _⟩

/-- The converse ("only if") direction of Lemma 3, for edges that are shortest paths. -/
theorem IsWeightedVFTSpanner.wdist_le_of_adj {f t : ℕ} (hH : IsWeightedVFTSpanner G H w f t)
    {F : Finset V} (hF : #F ≤ f) {u v : V} (hu : u ∉ F) (hv : v ∉ F)
    (htight : (G.deleteVerts F).wdist w u v = w s(u, v)) :
    (H.deleteVerts F).wdist w u v ≤ t * w s(u, v) :=
  htight ▸ hH.2 F hF u v hu hv

/-- **Lemma 3 of Dinitz–Robelle** (weighted, vertex faults): `H ≤ G` is an `f`-VFT `t`-spanner iff
`d_{H \ F}(u, v) ≤ t · w(uv)` for every `F` with `|F| ≤ f` and every edge `uv` of `G` with
`u, v ∉ F` and `d_{G \ F}(u, v) = w(uv)`. -/
theorem isWeightedVFTSpanner_iff [Finite V] {f t : ℕ} (ht : 1 ≤ t) (hHG : H ≤ G) :
    IsWeightedVFTSpanner G H w f t ↔ ∀ F : Finset V, #F ≤ f → ∀ u v, G.Adj u v → u ∉ F →
      v ∉ F → (G.deleteVerts F).wdist w u v = w s(u, v) →
      (H.deleteVerts F).wdist w u v ≤ t * w s(u, v) := by
  refine ⟨fun hH F hF u v _ hu hv htight => hH.wdist_le_of_adj hF hu hv htight, fun h => ?_⟩
  refine ⟨hHG, fun F hF u v _ _ => wdist_le_mul_of_adj ht ?_ u v⟩
  exact wdist_le_mul_of_tight fun x y hxy htight => h F hF x y hxy.1 hxy.2.1 hxy.2.2 htight

/-! ### Spanners with a real stretch -/

section

variable {u v : V}

/-- `H` is a `t`-spanner of the weighted graph `(G, w)`, for a real stretch `t`:
`H ≤ G` and `d_H(u, v) ≤ t · d_G(u, v)` for all `u, v`. -/
def IsWSpanner (G H : SimpleGraph V) (w : Sym2 V → ℝ≥0) (t : ℝ≥0) : Prop :=
  H ≤ G ∧ ∀ u v, H.wdist w u v ≤ t * G.wdist w u v

/-- A `t`-spanner stretches every edge of `G` by at most `t`. -/
theorem IsWSpanner.wdist_le_of_adj {t : ℝ≥0} (h : IsWSpanner G H w t) {x y : V}
    (hxy : G.Adj x y) : H.wdist w x y ≤ t * w s(x, y) :=
  (h.2 x y).trans (mul_le_mul_right (SimpleGraph.wdist_le_of_adj hxy) _)

/-- **Local criterion**: it suffices to check the stretch on the edges of `G`. -/
theorem isWSpanner_of_adj {t : ℝ≥0} (ht : 1 ≤ t) (hHG : H ≤ G)
    (h : ∀ x y, G.Adj x y → H.wdist w x y ≤ t * w s(x, y)) : IsWSpanner G H w t := by
  have ht0 : t ≠ 0 := (lt_of_lt_of_le one_pos ht).ne'
  refine ⟨hHG, fun u v => ?_⟩
  rw [← wdist_smul ht0]
  exact wdist_le_wdist_of_forall_adj fun a b hab => by simpa using h a b hab

/-- Every graph is a `t`-spanner of itself, for `t ≥ 1`. -/
theorem isWSpanner_refl {t : ℝ≥0} (ht : 1 ≤ t) : IsWSpanner G G w t :=
  ⟨le_rfl, fun _ _ => le_mul_of_one_le_left zero_le (by exact_mod_cast ht)⟩

/-- A spanner preserves connectivity. -/
theorem IsWSpanner.reachable {t : ℝ≥0} (hH : IsWSpanner G H w t) (h : G.Reachable u v) :
    H.Reachable u v :=
  reachable_of_wdist_lt_top ((hH.2 u v).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (wdist_lt_top_of_reachable h)))

/-! ### Bridges: natural stretches and unit weights -/

/-- A natural stretch `t` is the real stretch `(t : ℝ≥0)`: a `t`-spanner is a `0`-fault-tolerant
`t`-spanner. -/
theorem isWSpanner_natCast_iff {t : ℕ} :
    IsWSpanner G H w t ↔ IsWeightedVFTSpanner G H w 0 t := by
  simp only [IsWSpanner, IsWeightedVFTSpanner, ENNReal.coe_natCast, Nat.le_zero, card_eq_zero]
  refine and_congr_right fun _ => ⟨fun h F hF u v _ _ => by simpa [hF] using h u v,
    fun h u v => by simpa using h ∅ rfl u v (by simp) (by simp)⟩

private theorem toENNReal_le_natCast_mul_iff {a b : ℕ∞} {t : ℕ} :
    (a : ℝ≥0∞) ≤ t * b ↔ a ≤ t * b := by
  rw [← ENat.toENNReal_coe t, ← ENat.toENNReal_mul, ENat.toENNReal_le]

/-- With unit weights, CSLib's weighted VFT spanners are its unweighted VFT spanners. -/
theorem isWeightedVFTSpanner_one_iff {f t : ℕ} :
    IsWeightedVFTSpanner G H (fun _ => 1) f t ↔ IsVFTSpanner G H f t := by
  simp only [IsWeightedVFTSpanner, IsVFTSpanner, wdist_one, toENNReal_le_natCast_mul_iff]

/-- With unit weights, CSLib's weighted EFT spanners are its unweighted EFT spanners. -/
theorem isWeightedEFTSpanner_one_iff {f t : ℕ} :
    IsWeightedEFTSpanner G H (fun _ => 1) f t ↔ IsEFTSpanner G H f t := by
  simp only [IsWeightedEFTSpanner, IsEFTSpanner, wdist_one, toENNReal_le_natCast_mul_iff]

end

end SimpleGraph
