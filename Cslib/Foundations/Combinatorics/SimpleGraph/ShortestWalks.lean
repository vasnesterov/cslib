/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Shortest walks avoiding a set of edges, and dart weights

Tools for "replacement paths": walks of `G` that avoid a set `A` of (failed) edges and are shortest
in `G \ A`. Working with walks of `G` (rather than of `G.deleteEdges A`) lets walks for different
fault sets live in the same type `G.Walk u v`.

## Main definitions

* `SimpleGraph.Walk.Avoids A p`: no edge of `p` lies in `A`.
* `SimpleGraph.Walk.IsShortestIn A p`: `p` avoids `A` and `|p| = d_{G \ A}(u, v)` (as `ℕ∞`).
* `SimpleGraph.Walk.dwt w p`: the weight of a walk w.r.t. a *directed* weight `w : V → V → ℝ` on
  darts.

## Main results

* `IsShortestIn.append_left/right`, `.reverse`, `.isPath`, `.mono`: basic closure properties.
* `exists_eq_append_cons_of_mem_darts`: split a walk at a dart.
* `IsShortestIn.edist_snd`: along a shortest walk from `u`, every dart goes one step away from `u`.
* `IsShortestIn.dart_eq_of_edge_eq`: two shortest walks from the same vertex traverse a common
  edge in the same direction.
* `IsShortestIn.exists_mem_edges_not_mem`: two distinct shortest `u`–`v` walks have different
  edge sets.
* `dwt_bypass_le`: if all short closed walks have positive weight, bypassing a walk does not
  increase its weight.
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace Walk

/-- The walk `p` uses no edge of `A`. -/
def Avoids (A : Set (Sym2 V)) {u v : V} (p : G.Walk u v) : Prop := ∀ e ∈ p.edges, e ∉ A

/-- `p` is a shortest walk of `G \ A`: it avoids `A` and its length is `d_{G \ A}(u, v)`. -/
def IsShortestIn (A : Set (Sym2 V)) {u v : V} (p : G.Walk u v) : Prop :=
  p.Avoids A ∧ (p.length : ℕ∞) = (G.deleteEdges A).edist u v

variable {A B : Set (Sym2 V)} {u v w x : V}

@[simp] lemma avoids_nil : (nil : G.Walk u u).Avoids A := by simp [Avoids]

@[simp] lemma avoids_cons {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).Avoids A ↔ s(u, v) ∉ A ∧ p.Avoids A := by
  simp [Avoids]

@[simp] lemma avoids_append {p : G.Walk u v} {q : G.Walk v w} :
    (p.append q).Avoids A ↔ p.Avoids A ∧ q.Avoids A := by
  simp only [Avoids, edges_append, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (.inl he), fun e he => h e (.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

@[simp] lemma avoids_reverse {p : G.Walk u v} : p.reverse.Avoids A ↔ p.Avoids A := by
  simp [Avoids]

lemma Avoids.mono {p : G.Walk u v} (h : p.Avoids B) (hAB : A ⊆ B) : p.Avoids A :=
  fun e he hA => h e he (hAB hA)

lemma avoids_union {p : G.Walk u v} : p.Avoids (A ∪ B) ↔ p.Avoids A ∧ p.Avoids B := by
  simp only [Avoids, Set.mem_union, not_or]
  exact ⟨fun h => ⟨fun e he => (h e he).1, fun e he => (h e he).2⟩,
    fun h e he => ⟨h.1 e he, h.2 e he⟩⟩

lemma avoids_insert {e : Sym2 V} {p : G.Walk u v} :
    p.Avoids (insert e A) ↔ e ∉ p.edges ∧ p.Avoids A := by
  simp only [Avoids, Set.mem_insert_iff, not_or]
  exact ⟨fun h => ⟨fun he => (h e he).1 rfl, fun e' he => (h e' he).2⟩,
    fun h e' he => ⟨fun h' => h.1 (h' ▸ he), h.2 e' he⟩⟩

/-- A walk avoiding `A` bounds the distance in `G \ A`. -/
lemma Avoids.edist_le {p : G.Walk u v} (h : p.Avoids A) :
    (G.deleteEdges A).edist u v ≤ p.length := by
  simpa using (G.deleteEdges A).edist_le (p.toDeleteEdges A h)

lemma Avoids.reachable {p : G.Walk u v} (h : p.Avoids A) : (G.deleteEdges A).Reachable u v :=
  ⟨p.toDeleteEdges A h⟩

/-- A walk of `G \ A`, seen as a walk of `G`, avoids `A`. -/
lemma avoids_mapLe (p : (G.deleteEdges A).Walk u v) :
    (p.mapLe (G.deleteEdges_le A)).Avoids A := by
  intro e he hA
  rw [edges_mapLe_eq_edges] at he
  have := p.edges_subset_edgeSet he
  rw [edgeSet_deleteEdges] at this
  exact this.2 hA

/-- Every pair connected in `G \ A` is joined by a shortest walk of `G \ A`. -/
lemma exists_isShortestIn (h : (G.deleteEdges A).Reachable u v) :
    ∃ p : G.Walk u v, p.IsShortestIn A := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_edist
  exact ⟨p.mapLe (G.deleteEdges_le A), avoids_mapLe p, by simpa using hp⟩

/-- A walk avoiding `A` whose length is at most `d_{G \ A}` is shortest. -/
lemma Avoids.isShortestIn {p : G.Walk u v} (h : p.Avoids A)
    (hl : (p.length : ℕ∞) ≤ (G.deleteEdges A).edist u v) : p.IsShortestIn A :=
  ⟨h, le_antisymm hl h.edist_le⟩

private lemma enat_split {a b : ℕ∞} {x y : ℕ} (ha : a ≤ x) (hb : b ≤ y)
    (h : ((x + y : ℕ) : ℕ∞) ≤ a + b) : a = x ∧ b = y := by
  obtain ⟨a, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top x) ha)
  obtain ⟨b, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top y) hb)
  norm_cast at *
  constructor <;> omega

lemma IsShortestIn.append {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsShortestIn A) : p.IsShortestIn A ∧ q.IsShortestIn A := by
  obtain ⟨hav, hl⟩ := h
  rw [avoids_append] at hav
  have htri := (G.deleteEdges A).edist_triangle (u := u) (v := v) (w := w)
  rw [← hl, length_append] at htri
  obtain ⟨h1, h2⟩ := enat_split hav.1.edist_le hav.2.edist_le htri
  exact ⟨⟨hav.1, h1.symm⟩, ⟨hav.2, h2.symm⟩⟩

lemma IsShortestIn.append_left {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsShortestIn A) : p.IsShortestIn A := h.append.1

lemma IsShortestIn.append_right {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsShortestIn A) : q.IsShortestIn A := h.append.2

lemma IsShortestIn.reverse {p : G.Walk u v} (h : p.IsShortestIn A) : p.reverse.IsShortestIn A :=
  ⟨avoids_reverse.mpr h.1, by rw [length_reverse, h.2, edist_comm]⟩

lemma IsShortestIn.edist_ne_top {p : G.Walk u v} (h : p.IsShortestIn A) :
    (G.deleteEdges A).edist u v ≠ ⊤ := by
  rw [← h.2]; exact ENat.natCast_ne_top _

/-- A shortest walk avoiding the larger fault set `B ⊇ A` stays shortest for `B`. -/
lemma IsShortestIn.mono {p : G.Walk u v} (h : p.IsShortestIn A) (hAB : A ⊆ B)
    (hB : p.Avoids B) : p.IsShortestIn B := by
  refine hB.isShortestIn ?_
  rw [h.2]
  exact edist_anti (deleteEdges_anti hAB)

lemma IsShortestIn.isPath {p : G.Walk u v} (h : p.IsShortestIn A) : p.IsPath := by
  classical
  have hb : p.bypass.Avoids A := fun e he => h.1 e (p.edges_bypass_subset_edges he)
  have : p.length ≤ p.bypass.length := by
    have := hb.edist_le
    rw [← h.2] at this
    exact_mod_cast this
  rw [length_le_bypass_length_iff] at this
  rw [← this]
  exact p.bypass_isPath

lemma IsShortestIn.nil_iff {p : G.Walk u u} (h : p.IsShortestIn A) : p = nil := by
  have := h.2
  rw [edist_self] at this
  exact (length_eq_zero_iff.mp (by exact_mod_cast this)).eq_nil

/-- Split a walk at one of its darts. -/
lemma exists_eq_append_cons_of_mem_darts {p : G.Walk u v} {d : G.Dart} (hd : d ∈ p.darts) :
    ∃ (p₁ : G.Walk u d.fst) (p₂ : G.Walk d.snd v), p = p₁.append (cons d.adj p₂) := by
  induction p with
  | nil => simp at hd
  | @cons a b c hab q ih =>
    rw [darts_cons, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact ⟨nil, q, rfl⟩
    · obtain ⟨p₁, p₂, rfl⟩ := ih hd
      exact ⟨cons hab p₁, p₂, rfl⟩

/-- Along a shortest walk from `u`, every dart leads one step farther from `u`. -/
lemma IsShortestIn.edist_snd {p : G.Walk u v} (h : p.IsShortestIn A) {d : G.Dart}
    (hd : d ∈ p.darts) :
    (G.deleteEdges A).edist u d.snd = (G.deleteEdges A).edist u d.fst + 1 := by
  obtain ⟨p₁, p₂, rfl⟩ := exists_eq_append_cons_of_mem_darts hd
  have h1 := h.append_left
  have h2 : (p₁.append (cons d.adj nil)).IsShortestIn A := by
    have : (p₁.append (cons d.adj p₂)) = (p₁.append (cons d.adj nil)).append p₂ := by
      rw [← append_assoc]; rfl
    rw [this] at h
    exact h.append_left
  rw [← h1.2, ← h2.2, length_append]
  simp

lemma IsShortestIn.dart_eq_of_edge_eq {v' : V} {p : G.Walk u v} {q : G.Walk u v'}
    (hp : p.IsShortestIn A) (hq : q.IsShortestIn A) {d d' : G.Dart} (hd : d ∈ p.darts)
    (hd' : d' ∈ q.darts) (he : d.edge = d'.edge) : d = d' := by
  rcases (dart_edge_eq_iff d d').mp he with h | h
  · exact h
  exfalso
  have h1 := hp.edist_snd hd
  have h2 := hq.edist_snd hd'
  rw [h] at h1
  change (G.deleteEdges A).edist u d'.fst = (G.deleteEdges A).edist u d'.snd + 1 at h1
  rw [h1] at h2
  obtain ⟨q₁, q₂, hq'⟩ := exists_eq_append_cons_of_mem_darts hd'
  rw [hq'] at hq
  have hle := hq.append_left.1.edist_le
  rw [h1] at hle
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (G.deleteEdges A).edist u d'.snd = b := by
    refine (ENat.ne_top_iff_exists.mp ?_).imp fun _ h => h.symm
    intro htop; rw [htop] at hle; simp at hle
  rw [hb] at h2
  norm_cast at h2
  omega

/-- On a path, the first vertex is the start of the first dart only. -/
private lemma eq_of_mem_darts_of_fst_eq {a b c : V} {hab : G.Adj a b} {q : G.Walk b c}
    (hp : (cons hab q).IsPath) {d : G.Dart} (hd : d ∈ (cons hab q).darts) (hf : d.fst = a) :
    d = ⟨(a, b), hab⟩ := by
  rw [darts_cons, List.mem_cons] at hd
  rcases hd with rfl | hd
  · rfl
  · exfalso
    have := q.dart_fst_mem_support_of_mem_darts hd
    rw [hf] at this
    exact ((cons_isPath_iff _ _).mp hp).2 this

/-- Distinct shortest `u`–`v` walks of `G \ A` have different edge sets. -/
lemma IsShortestIn.eq_of_edges_subset {p q : G.Walk u v} (hp : p.IsShortestIn A)
    (hq : q.IsShortestIn A) (hsub : ∀ e ∈ p.edges, e ∈ q.edges) : p = q := by
  induction p with
  | nil => exact (hq.nil_iff).symm
  | @cons a b c hab p' ih =>
    cases q with
    | nil =>
      exfalso
      have := hp.2
      rw [edist_self] at this
      simp at this
    | @cons _ b' _ hab' q' =>
      have hpath := hp.isPath
      have hqpath := hq.isPath
      -- the first dart of `p` occurs in `q`
      have he : s(a, b) ∈ (cons hab' q').edges := hsub _ (by simp)
      obtain ⟨d', hd', hde⟩ := List.mem_map.mp he
      have hd0 : (⟨(a, b), hab⟩ : G.Dart) ∈ (cons hab p').darts := by simp
      have heq := hp.dart_eq_of_edge_eq hq hd0 hd' hde.symm
      have hfst : d'.fst = a := by rw [← heq]
      have := eq_of_mem_darts_of_fst_eq hqpath hd' hfst
      rw [this] at heq
      simp only [Dart.mk.injEq, Prod.mk.injEq, true_and] at heq
      subst heq
      have hp' : p'.IsShortestIn A := by
        have : cons hab p' = (cons hab nil).append p' := rfl
        rw [this] at hp; exact hp.append_right
      have hq' : q'.IsShortestIn A := by
        have : cons hab' q' = (cons hab' nil).append q' := rfl
        rw [this] at hq; exact hq.append_right
      have hsub' : ∀ e ∈ p'.edges, e ∈ q'.edges := by
        intro e he'
        have := hsub e (by simp [he'])
        rw [edges_cons, List.mem_cons] at this
        rcases this with rfl | h
        · exfalso
          have hn := hpath.isTrail.edges_nodup
          rw [edges_cons, List.nodup_cons] at hn
          exact hn.1 he'
        · exact h
      rw [ih hp' hq' hsub']

/-- Two distinct shortest `u`–`v` walks of `G \ A`: the first has an edge the second lacks. -/
lemma IsShortestIn.exists_mem_edges_not_mem {p q : G.Walk u v}
    (hp : p.IsShortestIn A) (hq : q.IsShortestIn A) (hne : p ≠ q) :
    ∃ e ∈ p.edges, e ∉ q.edges := by
  by_contra h
  push Not at h
  exact hne (hp.eq_of_edges_subset hq h)

/-- If `Q` holds at the start and fails at the end of a walk, some dart goes from a `Q`-vertex to
a non-`Q`-vertex. -/
lemma exists_dart_of_pred (Q : V → Prop) (p : G.Walk u v) (hu : Q u) (hv : ¬ Q v) :
    ∃ (x y : V) (h : G.Adj x y) (p₁ : G.Walk u x) (p₂ : G.Walk y v),
      p = p₁.append (cons h p₂) ∧ Q x ∧ ¬ Q y := by
  induction p with
  | nil => exact absurd hu hv
  | @cons a b c hab q ih =>
    by_cases hb : Q b
    · obtain ⟨x, y, h, p₁, p₂, rfl, hx, hy⟩ := ih hb hv
      exact ⟨x, y, h, cons hab p₁, p₂, rfl, hx, hy⟩
    · exact ⟨a, b, hab, nil, q, rfl, hu, hb⟩

/-! ### Directed dart weights -/

/-- Weight of a walk w.r.t. a directed weight `w` on darts. -/
def dwt (w : V → V → ℝ) (p : G.Walk u v) : ℝ := (p.darts.map fun d => w d.fst d.snd).sum

variable (w' : V → V → ℝ)

@[simp] lemma dwt_nil : (nil : G.Walk u u).dwt w' = 0 := by simp [dwt]

@[simp] lemma dwt_cons (h : G.Adj u v) (p : G.Walk v x) :
    (cons h p).dwt w' = w' u v + p.dwt w' := by simp [dwt]

@[simp] lemma dwt_append (p : G.Walk u v) (q : G.Walk v x) :
    (p.append q).dwt w' = p.dwt w' + q.dwt w' := by simp [dwt, darts_append]

/-- Reversing a walk: if `w(a,b) + w(b,a) = c` on every edge, then `w(rev p) = c|p| - w(p)`. -/
lemma dwt_reverse {c : ℝ} (hw : ∀ a b, G.Adj a b → w' a b + w' b a = c) (p : G.Walk u v) :
    p.reverse.dwt w' = c * p.length - p.dwt w' := by
  induction p with
  | nil => simp
  | @cons a b d hab q ih =>
    rw [reverse_cons, dwt_append, ih, dwt_cons, dwt_cons, dwt_nil, length_cons, ← hw a b hab]
    push_cast; ring

lemma dwt_le_length_mul {c : ℝ} (p : G.Walk u v) (h : ∀ a b, G.Adj a b → w' a b ≤ c) :
    p.dwt w' ≤ p.length * c := by
  induction p with
  | nil => simp
  | @cons a b d hab q ih => rw [dwt_cons, length_cons]; push_cast; linarith [h a b hab]

lemma length_mul_le_dwt {c : ℝ} (p : G.Walk u v) (h : ∀ a b, G.Adj a b → c ≤ w' a b) :
    p.length * c ≤ p.dwt w' := by
  induction p with
  | nil => simp
  | @cons a b d hab q ih => rw [dwt_cons, length_cons]; push_cast; linarith [h a b hab]

/-- **Bypassing does not increase the weight** when closed walks have positive weight. If every
closed walk of positive length `≤ N` has positive `w'`-weight, then for every walk `q` of length
`≤ N`, `w'(bypass q) ≤ w'(q)`, strictly if `bypass q ≠ q`. -/
lemma dwt_bypass_le [DecidableEq V] (N : ℕ)
    (hpos : ∀ (x : V) (c : G.Walk x x), 0 < c.length → c.length ≤ N → 0 < c.dwt w') :
    ∀ {u v : V} (q : G.Walk u v), q.length ≤ N →
      q.bypass.dwt w' ≤ q.dwt w' ∧ (q.bypass ≠ q → q.bypass.dwt w' < q.dwt w') := by
  intro u v q
  induction q with
  | nil => simp [bypass]
  | @cons a b c hab p ih =>
    intro hlen
    rw [length_cons] at hlen
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    simp only [bypass]
    split_ifs with hs
    · -- a closed walk `a → b ⇝ a` is cut out
      have hsplit := p.bypass.take_spec hs
      have hc := hpos a (cons hab (p.bypass.takeUntil a hs)) (by simp) (by
        have := p.bypass.length_takeUntil_le_length hs
        have := p.length_bypass_le_length
        simp only [length_cons]; omega)
      have hw : p.bypass.dwt w' =
          (p.bypass.takeUntil a hs).dwt w' + (p.bypass.dropUntil a hs).dwt w' := by
        conv_lhs => rw [← hsplit]
        rw [dwt_append]
      rw [dwt_cons] at hc ⊢
      constructor <;> [skip; intro _] <;> linarith
    · refine ⟨by rw [dwt_cons, dwt_cons]; linarith, fun hne => ?_⟩
      have : p.bypass ≠ p := fun h => hne (by rw [h])
      rw [dwt_cons, dwt_cons]
      linarith [ih2 this]

end Walk

end SimpleGraph
