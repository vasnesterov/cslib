/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Foundations.Combinatorics.SimpleGraph.Spanner
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Basic.ENNReal.BigOperators

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
  have key : ∀ p : G.Walk u v, H.wdist w u v ≤ t * p.wlength w :=
    fun p => wdist_le_mul_wlength p fun a b hab _ => h a b hab
  change _ ≤ (t : ℝ≥0∞) * ⨅ p : G.Walk u v, p.wlength w
  rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast (by omega : t ≠ 0)) (by simp)]
  exact le_iInf key

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

end SimpleGraph
