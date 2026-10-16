/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Walks of prescribed length and parity distances

For a simple graph `G` and a vertex `s`:

* `SimpleGraph.walkSet G s t`: the set of vertices reachable from `s` by a walk of length exactly
  `t` (defined by recursion on `t`; `mem_walkSet_iff` relates it to `G.Walk`).
* `SimpleGraph.IsParityDist G s v t`: `t` is the length of a shortest walk from `s` to `v`
  *among the walks of length `≡ t (mod 2)`*. Equivalently, `t` is the distance from `(s, 0)` to
  `(v, t mod 2)` in the bipartite double cover `G × K₂`. Every vertex has at most one parity
  distance of each parity (`IsParityDist.eq_of_mod_two_eq`).

## Main results

* `Reachable.isParityDist_dist`: the ordinary distance is a parity distance.
* `mod_two_eq_of_colorable`: in a bipartite graph all walks between two vertices have the same
  parity, so the ordinary distance is the only parity distance
  (`IsParityDist.eq_dist_of_colorable`).
* `exists_mem_walkSet_of_not_colorable`: in a connected non-bipartite graph every vertex is
  reached by walks of both parities.
* `exists_isParityDist`: a walk of length `t` gives a parity distance `≤ t` of the same parity.
* `IsAcyclic.eq_of_dist_add_one`: in a forest every vertex has at most one neighbour that is one
  step closer to a given vertex.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- `G.walkSet s t` is the set of vertices `v` such that there is a walk of length exactly `t`
from `s` to `v`. -/
def walkSet (s : V) : ℕ → Set V
  | 0 => {s}
  | t + 1 => {w | ∃ v ∈ walkSet s t, G.Adj v w}

variable {G}

@[simp] lemma walkSet_zero (s : V) : G.walkSet s 0 = {s} := rfl

lemma mem_walkSet_succ {s w : V} {t : ℕ} :
    w ∈ G.walkSet s (t + 1) ↔ ∃ v ∈ G.walkSet s t, G.Adj v w := Iff.rfl

lemma mem_walkSet_succ' {s w : V} {t : ℕ} :
    w ∈ G.walkSet s (t + 1) ↔ ∃ u, G.Adj s u ∧ w ∈ G.walkSet u t := by
  induction t generalizing w with
  | zero => simp [mem_walkSet_succ]
  | succ t ih =>
    rw [mem_walkSet_succ]
    constructor
    · rintro ⟨v, hv, hvw⟩
      obtain ⟨u, hsu, hu⟩ := ih.1 hv
      exact ⟨u, hsu, v, hu, hvw⟩
    · rintro ⟨u, hsu, v, hv, hvw⟩
      exact ⟨v, ih.2 ⟨u, hsu, hv⟩, hvw⟩

/-- `walkSet` is the set of endpoints of walks of length `t`. -/
lemma mem_walkSet_iff {s v : V} {t : ℕ} :
    v ∈ G.walkSet s t ↔ ∃ p : G.Walk s v, p.length = t := by
  induction t generalizing s with
  | zero =>
    constructor
    · rintro rfl; exact ⟨.nil, rfl⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => rfl
      | cons _ _ => simp at hp
  | succ t ih =>
    rw [mem_walkSet_succ']
    constructor
    · rintro ⟨u, hsu, hu⟩
      obtain ⟨p, hp⟩ := ih.1 hu
      exact ⟨.cons hsu p, by simp [hp]⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => simp at hp
      | cons h q => exact ⟨_, h, ih.2 ⟨q, by simpa using hp⟩⟩

lemma Walk.mem_walkSet {s v : V} (p : G.Walk s v) : v ∈ G.walkSet s p.length :=
  mem_walkSet_iff.2 ⟨p, rfl⟩

lemma mem_walkSet_succ_of_adj {s v w : V} {t : ℕ} (hv : v ∈ G.walkSet s t) (h : G.Adj v w) :
    w ∈ G.walkSet s (t + 1) := ⟨v, hv, h⟩

lemma mem_walkSet_add {s u v : V} {a b : ℕ} (hu : u ∈ G.walkSet s a) (hv : v ∈ G.walkSet u b) :
    v ∈ G.walkSet s (a + b) := by
  obtain ⟨p, rfl⟩ := mem_walkSet_iff.1 hu
  obtain ⟨q, rfl⟩ := mem_walkSet_iff.1 hv
  simpa using (p.append q).mem_walkSet

lemma mem_walkSet_comm {s v : V} {t : ℕ} : v ∈ G.walkSet s t ↔ s ∈ G.walkSet v t := by
  simp only [mem_walkSet_iff]
  exact ⟨fun ⟨p, hp⟩ => ⟨p.reverse, by simpa⟩, fun ⟨p, hp⟩ => ⟨p.reverse, by simpa⟩⟩

lemma reachable_of_mem_walkSet {s v : V} {t : ℕ} (h : v ∈ G.walkSet s t) : G.Reachable s v := by
  obtain ⟨p, -⟩ := mem_walkSet_iff.1 h
  exact ⟨p⟩

lemma edist_le_of_mem_walkSet {s v : V} {t : ℕ} (h : v ∈ G.walkSet s t) : G.edist s v ≤ t := by
  obtain ⟨p, rfl⟩ := mem_walkSet_iff.1 h
  exact edist_le p

lemma dist_le_of_mem_walkSet {s v : V} {t : ℕ} (h : v ∈ G.walkSet s t) : G.dist s v ≤ t := by
  obtain ⟨p, rfl⟩ := mem_walkSet_iff.1 h
  exact dist_le p

lemma Reachable.mem_walkSet_dist {s v : V} (h : G.Reachable s v) :
    v ∈ G.walkSet s (G.dist s v) := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  exact hp ▸ p.mem_walkSet

/-- `t` is a *parity distance* from `s` to `v`: there is a walk of length `t` from `s` to `v`, and
no shorter walk of the same parity. -/
def IsParityDist (G : SimpleGraph V) (s v : V) (t : ℕ) : Prop :=
  v ∈ G.walkSet s t ∧ ∀ t' < t, t' % 2 = t % 2 → v ∉ G.walkSet s t'

lemma IsParityDist.mem {s v : V} {t : ℕ} (h : G.IsParityDist s v t) : v ∈ G.walkSet s t := h.1

lemma IsParityDist.eq_of_mod_two_eq {s v : V} {t t' : ℕ} (h : G.IsParityDist s v t)
    (h' : G.IsParityDist s v t') (ht : t % 2 = t' % 2) : t = t' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.2 t hlt ht h.1
  · exact h.2 t' hlt ht.symm h'.1

lemma IsParityDist.le_of_mem {s v : V} {t t' : ℕ} (h : G.IsParityDist s v t)
    (h' : v ∈ G.walkSet s t') (ht : t' % 2 = t % 2) : t ≤ t' := by
  by_contra hlt
  exact h.2 t' (by omega) ht h'

@[simp] lemma isParityDist_zero_iff {s v : V} : G.IsParityDist s v 0 ↔ v = s := by
  simp [IsParityDist]

lemma dist_le_of_isParityDist {s v : V} {t : ℕ} (h : G.IsParityDist s v t) : G.dist s v ≤ t :=
  dist_le_of_mem_walkSet h.1

/-- The ordinary distance is a parity distance. -/
lemma Reachable.isParityDist_dist {s v : V} (h : G.Reachable s v) :
    G.IsParityDist s v (G.dist s v) :=
  ⟨h.mem_walkSet_dist, fun _ ht' _ hm => absurd (dist_le_of_mem_walkSet hm) (by omega)⟩

/-- Any walk of length `t` gives a parity distance `≤ t` of the same parity. -/
lemma exists_isParityDist {s v : V} {t : ℕ} (h : v ∈ G.walkSet s t) :
    ∃ t' ≤ t, t' % 2 = t % 2 ∧ G.IsParityDist s v t' := by
  classical
  have hex : ∃ n, n % 2 = t % 2 ∧ v ∈ G.walkSet s n := ⟨t, rfl, h⟩
  refine ⟨Nat.find hex, Nat.find_min' hex ⟨rfl, h⟩, (Nat.find_spec hex).1,
    (Nat.find_spec hex).2, fun t' ht' hpar hm => Nat.find_min hex ht' ⟨?_, hm⟩⟩
  rw [hpar, (Nat.find_spec hex).1]

/-- If `w` is adjacent to `v` and `t` is a parity distance of `v`, then `w` has a parity distance
of the opposite parity which is at most `t + 1`. -/
lemma IsParityDist.exists_adj {s v w : V} {t : ℕ} (h : G.IsParityDist s v t) (hvw : G.Adj v w) :
    ∃ t' ≤ t + 1, t' % 2 = (t + 1) % 2 ∧ G.IsParityDist s w t' :=
  exists_isParityDist (mem_walkSet_succ_of_adj h.1 hvw)

/-- In a bipartite graph all walks between two fixed vertices have lengths of the same parity. -/
lemma mod_two_eq_of_colorable (hG : G.Colorable 2) {s v : V} {t t' : ℕ}
    (h : v ∈ G.walkSet s t) (h' : v ∈ G.walkSet s t') : t % 2 = t' % 2 := by
  obtain ⟨p, rfl⟩ := mem_walkSet_iff.1 h
  obtain ⟨q, rfl⟩ := mem_walkSet_iff.1 h'
  have := two_colorable_iff_forall_loop_even.1 hG s (p.append q.reverse)
  simp only [Walk.length_append, Walk.length_reverse] at this
  rcases this with ⟨k, hk⟩
  omega

/-- In a bipartite graph the only parity distance is the distance. -/
lemma IsParityDist.eq_dist_of_colorable (hG : G.Colorable 2) {s v : V} {t : ℕ}
    (h : G.IsParityDist s v t) : t = G.dist s v :=
  h.eq_of_mod_two_eq (reachable_of_mem_walkSet h.1).isParityDist_dist
    (mod_two_eq_of_colorable hG h.1 (reachable_of_mem_walkSet h.1).mem_walkSet_dist)

/-- In a connected non-bipartite graph every vertex is reached by walks of both parities. -/
lemma exists_mem_walkSet_of_not_colorable (hc : G.Preconnected) (hG : ¬ G.Colorable 2)
    (s v : V) (b : ℕ) : ∃ t, t % 2 = b % 2 ∧ v ∈ G.walkSet s t := by
  rw [two_colorable_iff_forall_loop_even] at hG
  push Not at hG
  obtain ⟨u, c, hc'⟩ := hG
  rw [Nat.not_even_iff_odd] at hc'
  obtain ⟨p⟩ := hc s u
  obtain ⟨q⟩ := hc u v
  rcases Nat.even_or_odd (p.length + q.length + b + 1) with he | ho
  · refine ⟨p.length + c.length + q.length, ?_, mem_walkSet_add (mem_walkSet_add p.mem_walkSet
      c.mem_walkSet) q.mem_walkSet⟩
    rcases he with ⟨k, hk⟩; rcases hc' with ⟨m, hm⟩; omega
  · exact ⟨p.length + q.length, by rcases ho with ⟨k, hk⟩; omega,
      mem_walkSet_add p.mem_walkSet q.mem_walkSet⟩

/-- In a forest, a vertex `u` has at most one neighbour that is one step closer to `s`
(its BFS parent). -/
lemma IsAcyclic.eq_of_dist_add_one (hG : G.IsAcyclic) {s a b u : V} (ha : G.Adj a u)
    (hb : G.Adj b u) (hra : G.Reachable s a) (hrb : G.Reachable s b)
    (hda : G.dist s a + 1 = G.dist s u) (hdb : G.dist s b + 1 = G.dist s u) : a = b := by
  obtain ⟨p, hp⟩ := hra.exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := hrb.exists_walk_length_eq_dist
  have hp' : (p.concat ha).IsPath := (p.concat ha).isPath_of_length_eq_dist (by simp [hp, hda])
  have hq' : (q.concat hb).IsPath := (q.concat hb).isPath_of_length_eq_dist (by simp [hq, hdb])
  have := (hG.subsingleton_path s u).elim ⟨_, hp'⟩ ⟨_, hq'⟩
  obtain ⟨hv, -⟩ := Walk.concat_inj (congrArg Subtype.val this)
  exact hv

/-- Adjacent vertices have distances from `s` differing by at most one. -/
lemma Reachable.dist_le_dist_add_one_of_adj {s u v : V} (hu : G.Reachable s u) (h : G.Adj u v) :
    G.dist s v ≤ G.dist s u + 1 :=
  dist_le_of_mem_walkSet (mem_walkSet_succ_of_adj hu.mem_walkSet_dist h)

end SimpleGraph
