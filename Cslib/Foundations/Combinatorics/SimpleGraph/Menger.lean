/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Foundations.Combinatorics.SimpleGraph.VertexConnectivity
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Menger's theorem and the fan lemma

Mathlib has no vertex version of Menger's theorem.

## Main results

* `SimpleGraph.menger`: Menger's theorem, set version: if every `A`–`B` separator has at least
  `k` vertices, then there are `k` pairwise vertex-disjoint `A`–`B` paths.
* `SimpleGraph.fan`, `SimpleGraph.IsVertexConnected.fan`: the fan lemma.

## Implementation notes

The proof of Menger's theorem is Göring's short proof (Diestel, *Graph Theory*, Thm. 3.3.1, first
proof), by induction on the number of edges. Instead of contracting an edge `xy` (which would
change the vertex type) we *merge* `y` into `x` on the same vertex type: `y` becomes isolated and
its neighbours are attached to `x` (`SimpleGraph.mergeGraph`). Internally we work with families
of pairwise disjoint *walks* (`SimpleGraph.DisjointWalks`), and shortcut them to paths at the end.

## References

* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Theorem 3.3.1.
* F. Göring, *Short proof of Menger's theorem*, Discrete Mathematics 219 (2000).
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

section Basic

variable {G : SimpleGraph V}

namespace Walk

/-- All vertices of the walk lie outside `Z`, except possibly its final vertex (more precisely:
each step of the walk starts outside `Z`). -/
def AvoidsBeforeEnd (Z : Set V) : ∀ {u w : V}, G.Walk u w → Prop
  | _, _, .nil => True
  | u, _, .cons _ p => u ∉ Z ∧ AvoidsBeforeEnd Z p

@[simp] lemma avoidsBeforeEnd_nil {Z : Set V} {u : V} :
    (nil : G.Walk u u).AvoidsBeforeEnd Z := trivial

@[simp] lemma avoidsBeforeEnd_cons {Z : Set V} {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).AvoidsBeforeEnd Z ↔ u ∉ Z ∧ p.AvoidsBeforeEnd Z := Iff.rfl

lemma AvoidsBeforeEnd.eq_of_mem {Z : Set V} {u w : V} {p : G.Walk u w}
    (hp : p.AvoidsBeforeEnd Z) {v : V} (hv : v ∈ p.support) (hvZ : v ∈ Z) : v = w := by
  induction p with
  | nil => simpa using hv
  | cons h p ih =>
    simp only [support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact absurd hvZ hp.1
    · exact ih hp.2 hv

lemma AvoidsBeforeEnd.reachableAvoiding {Z : Set V} {u w : V} {p : G.Walk u w}
    (hp : p.AvoidsBeforeEnd Z) {v : V} (hv : v ∈ p.support) (hvZ : v ∉ Z) :
    G.ReachableAvoiding Z u v := by
  induction p with
  | nil =>
    simp only [support_nil, List.mem_singleton] at hv
    subst hv
    exact ⟨nil, by simpa using hvZ⟩
  | cons h p ih =>
    simp only [support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨nil, by simpa using hvZ⟩
    · obtain ⟨q, hq⟩ := ih hp.2 hv
      refine ⟨cons h q, fun x hx => ?_⟩
      simp only [support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      exacts [hp.1, hq x hx]

/-- Every walk that meets `Z` has a prefix ending at its first vertex in `Z`. -/
lemma exists_prefix_avoidsBeforeEnd {Z : Set V} {u w : V} (p : G.Walk u w)
    (h : ∃ v ∈ p.support, v ∈ Z) :
    ∃ z ∈ Z, ∃ q : G.Walk u z, (∀ v ∈ q.support, v ∈ p.support) ∧ q.AvoidsBeforeEnd Z := by
  classical
  induction p with
  | nil =>
    obtain ⟨v, hv, hvZ⟩ := h
    simp only [support_nil, List.mem_singleton] at hv
    subst hv
    exact ⟨_, hvZ, nil, by simp, trivial⟩
  | @cons u u₁ w hadj p ih =>
    by_cases hu : u ∈ Z
    · exact ⟨u, hu, nil, by simp, trivial⟩
    · obtain ⟨v, hv, hvZ⟩ := h
      simp only [support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact absurd hvZ hu
      obtain ⟨z, hz, q, hq₁, hq₂⟩ := ih ⟨v, hv, hvZ⟩
      refine ⟨z, hz, cons hadj q, fun x hx => ?_, hu, hq₂⟩
      simp only [support_cons, List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      exacts [Or.inl rfl, Or.inr (hq₁ x hx)]

end Walk

end Basic

section DisjointWalks

variable (G : SimpleGraph V)

/-- `G` contains `k` pairwise vertex-disjoint walks from `A` to `B`. -/
def DisjointWalks (A B : Finset V) (k : ℕ) : Prop :=
  ∃ (a b : Fin k → V) (p : ∀ i, G.Walk (a i) (b i)), (∀ i, a i ∈ A ∧ b i ∈ B) ∧
    ∀ i j, i ≠ j → ∀ v ∈ (p i).support, v ∉ (p j).support

variable {G}

lemma DisjointWalks.mono {H : SimpleGraph V} (hGH : G ≤ H) {A B : Finset V} {k : ℕ}
    (h : G.DisjointWalks A B k) : H.DisjointWalks A B k := by
  obtain ⟨a, b, p, hab, hp⟩ := h
  exact ⟨a, b, fun i => (p i).mapLe hGH, hab, by simpa [Walk.support_mapLe_eq_support] using hp⟩

/-- A family of disjoint walks from `A` to `Z` can be shortened to walks meeting `Z` only at
their ends. -/
lemma DisjointWalks.exists_avoidsBeforeEnd {A Z : Finset V} {k : ℕ} (h : G.DisjointWalks A Z k) :
    ∃ (a z : Fin k → V) (p : ∀ i, G.Walk (a i) (z i)), (∀ i, a i ∈ A ∧ z i ∈ Z) ∧
      (∀ i j, i ≠ j → ∀ v ∈ (p i).support, v ∉ (p j).support) ∧
      ∀ i, (p i).AvoidsBeforeEnd (Z : Set V) := by
  obtain ⟨a, b, p, hab, hp⟩ := h
  have := fun i => (p i).exists_prefix_avoidsBeforeEnd (Z := (Z : Set V))
    ⟨b i, (p i).end_mem_support, (hab i).2⟩
  choose z hz q hq₁ hq₂ using this
  exact ⟨a, z, q, fun i => ⟨(hab i).1, hz i⟩,
    fun i j hij v hv hv' => hp i j hij v (hq₁ i v hv) (hq₁ j v hv'), hq₂⟩

/-- Gluing step of Göring's proof: `k` disjoint `A`–`Z` walks and `k` disjoint `B`–`Z` walks
meeting the separator `Z` (of size at most `k`) only at their ends combine into `k` disjoint
`A`–`B` walks. -/
lemma disjointWalks_of_glue {A B Z : Finset V} {k : ℕ}
    (hZ : G.Separates (Z : Set V) A B) (hk : Z.card ≤ k)
    (a z : Fin k → V) (p : ∀ i, G.Walk (a i) (z i)) (ha : ∀ i, a i ∈ A) (hz : ∀ i, z i ∈ Z)
    (hpd : ∀ i j, i ≠ j → ∀ v ∈ (p i).support, v ∉ (p j).support)
    (hp : ∀ i, (p i).AvoidsBeforeEnd (Z : Set V))
    (b z' : Fin k → V) (q : ∀ i, G.Walk (b i) (z' i)) (hb : ∀ i, b i ∈ B) (hz' : ∀ i, z' i ∈ Z)
    (hqd : ∀ i j, i ≠ j → ∀ v ∈ (q i).support, v ∉ (q j).support)
    (hq : ∀ i, (q i).AvoidsBeforeEnd (Z : Set V)) :
    G.DisjointWalks A B k := by
  classical
  have cross : ∀ i j v, v ∈ (p i).support → v ∈ (q j).support → z i = z' j := by
    intro i j v hvp hvq
    by_cases hvZ : v ∈ (Z : Set V)
    · exact ((hp i).eq_of_mem hvp hvZ).symm.trans ((hq j).eq_of_mem hvq hvZ)
    · exact absurd (((hp i).reachableAvoiding hvp hvZ).trans
        ((hq j).reachableAvoiding hvq hvZ).symm) (hZ.not_reachableAvoiding (ha i) (hb j))
  have hzinj : ∀ i j, i ≠ j → z i ≠ z j := fun i j hij h =>
    hpd i j hij (z i) (p i).end_mem_support (by rw [h]; exact (p j).end_mem_support)
  have hz'inj : Function.Injective z' := fun i j h => by
    by_contra hij
    exact hqd i j hij (z' i) (q i).end_mem_support (by rw [h]; exact (q j).end_mem_support)
  have himg : Finset.univ.image z' = Z := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hx
      exact hz' j
    · rw [Finset.card_image_of_injective _ hz'inj, Finset.card_univ, Fintype.card_fin]
      exact hk
  have hsurj : ∀ i, ∃ j, z' j = z i := fun i => by
    have := hz i
    rw [← himg] at this
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 this
    exact ⟨j, hj⟩
  choose σ hσ using hsurj
  let r : ∀ i, G.Walk (a i) (b (σ i)) := fun i =>
    (p i).append ((q (σ i)).reverse.copy (hσ i) rfl)
  have hr : ∀ i v, v ∈ (r i).support ↔ v ∈ (p i).support ∨ v ∈ (q (σ i)).support := by
    intro i v
    simp [r, Walk.mem_support_append_iff, Walk.support_copy, Walk.support_reverse]
  refine ⟨a, fun i => b (σ i), r, fun i => ⟨ha i, hb _⟩, ?_⟩
  intro i j hij v hvi hvj
  rw [hr] at hvi hvj
  have hzij := hzinj i j hij
  rcases hvi with hvi | hvi <;> rcases hvj with hvj | hvj
  · exact hpd i j hij v hvi hvj
  · exact hzij ((cross i (σ j) v hvi hvj).trans (hσ j))
  · exact hzij ((cross j (σ i) v hvj hvi).trans (hσ i)).symm
  · have : σ i ≠ σ j := fun h => hzij (by rw [← hσ i, ← hσ j, h])
    exact hqd _ _ this v hvi hvj

end DisjointWalks

section DeleteEdge

variable {G : SimpleGraph V}

lemma Walk.AvoidsBeforeEnd.exists_deleteEdges {Z : Set V} {x y : V} (hx : x ∈ Z) (hy : y ∈ Z)
    {u w : V} {p : G.Walk u w} (hp : p.AvoidsBeforeEnd Z) :
    ∃ q : (G.deleteEdges {s(x, y)}).Walk u w, q.support = p.support := by
  induction p with
  | nil => exact ⟨Walk.nil, rfl⟩
  | @cons u v w h p ih =>
    obtain ⟨q, hq⟩ := ih hp.2
    have hadj : (G.deleteEdges {s(x, y)}).Adj u v := by
      rw [deleteEdges_adj]
      refine ⟨h, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
      rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
      exacts [hp.1 hx, hp.1 hy]
    exact ⟨Walk.cons hadj q, by simp [hq]⟩

/-- If `Z ∋ x, y` separates `A` from `B` in `G`, then every `A`–`Z` separator in `G - xy` is an
`A`–`B` separator in `G`. -/
lemma Separates.of_deleteEdges {A B Z W : Set V} {x y : V} (hZ : G.Separates Z A B)
    (hx : x ∈ Z) (hy : y ∈ Z) (hW : (G.deleteEdges {s(x, y)}).Separates W A Z) :
    G.Separates W A B := by
  intro a ha b hb p
  obtain ⟨z, hz, q, hq₁, hq₂⟩ := p.exists_prefix_avoidsBeforeEnd (hZ a ha b hb p)
  obtain ⟨q', hq'⟩ := hq₂.exists_deleteEdges hx hy
  obtain ⟨v, hv, hvW⟩ := hW a ha z hz q'
  exact ⟨v, hq₁ v (hq' ▸ hv), hvW⟩

end DeleteEdge

section Merge

variable (G : SimpleGraph V) (x y : V)

/-- The graph obtained from `G` by merging `y` into `x` (a substitute for the contraction of the
edge `xy` that keeps the vertex type): `y` becomes isolated and every neighbour of `y` becomes a
neighbour of `x`. -/
def mergeGraph : SimpleGraph V where
  Adj u w := u ≠ w ∧ u ≠ y ∧ w ≠ y ∧ (G.Adj u w ∨ (u = x ∧ G.Adj y w) ∨ (w = x ∧ G.Adj u y))
  symm := ⟨fun u w ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁.symm, h₃, h₂, by
    rcases h₄ with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨rfl, h.symm⟩)
    · exact Or.inr (Or.inl ⟨rfl, h.symm⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable [DecidableEq V]

/-- The vertex map of `mergeGraph`: `y ↦ x`, other vertices are fixed. -/
def mergeMap (v : V) : V := if v = y then x else v

variable {G x y}

@[simp] lemma mergeMap_self : mergeMap x y y = x := by simp [mergeMap]

lemma mergeMap_of_ne {v : V} (hv : v ≠ y) : mergeMap x y v = v := by simp [mergeMap, hv]

lemma mergeMap_ne (hxy : x ≠ y) (v : V) : mergeMap x y v ≠ y := by
  unfold mergeMap; split_ifs with h
  · exact hxy
  · exact h

lemma mergeGraph_adj_of_adj (hxy : x ≠ y) {u v : V} (h : G.Adj u v)
    (hne : mergeMap x y u ≠ mergeMap x y v) :
    (G.mergeGraph x y).Adj (mergeMap x y u) (mergeMap x y v) := by
  refine ⟨hne, mergeMap_ne hxy u, mergeMap_ne hxy v, ?_⟩
  by_cases hu : u = y <;> by_cases hv : v = y
  · subst hu; subst hv; exact absurd h (G.loopless.irrefl _)
  · subst hu; rw [mergeMap_self, mergeMap_of_ne hv]; exact Or.inr (Or.inl ⟨rfl, h⟩)
  · subst hv; rw [mergeMap_self, mergeMap_of_ne hu]; exact Or.inr (Or.inr ⟨rfl, h⟩)
  · rw [mergeMap_of_ne hu, mergeMap_of_ne hv]; exact Or.inl h

lemma exists_adj_of_mergeGraph_adj {u v : V} (h : (G.mergeGraph x y).Adj u v) :
    ∃ u₁ v₁, mergeMap x y u₁ = u ∧ mergeMap x y v₁ = v ∧ G.Adj u₁ v₁ := by
  obtain ⟨-, hu, hv, h | ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ := h
  · exact ⟨u, v, mergeMap_of_ne hu, mergeMap_of_ne hv, h⟩
  · exact ⟨y, v, mergeMap_self, mergeMap_of_ne hv, h⟩
  · exact ⟨u, y, mergeMap_of_ne hu, mergeMap_self, h⟩

lemma exists_walk_of_mergeMap_eq (hxy : G.Adj x y) {u₀ u₁ : V}
    (h : mergeMap x y u₀ = mergeMap x y u₁) :
    ∃ r : G.Walk u₀ u₁, ∀ v ∈ r.support, mergeMap x y v = mergeMap x y u₀ := by
  by_cases h₀₁ : u₀ = u₁
  · subst h₀₁; exact ⟨Walk.nil, by simp⟩
  by_cases h₀ : u₀ = y <;> by_cases h₁ : u₁ = y
  · exact absurd (h₀.trans h₁.symm) h₀₁
  · subst h₀
    rw [mergeMap_self, mergeMap_of_ne h₁] at h
    subst h
    refine ⟨Walk.cons hxy.symm Walk.nil, fun v hv => ?_⟩
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | rfl <;> simp [mergeMap_of_ne h₁]
  · subst h₁
    rw [mergeMap_self, mergeMap_of_ne h₀] at h
    subst h
    refine ⟨Walk.cons hxy Walk.nil, fun v hv => ?_⟩
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | rfl <;> simp [mergeMap_of_ne h₀]
  · rw [mergeMap_of_ne h₀, mergeMap_of_ne h₁] at h
    exact absurd h h₀₁

/-- Walks of `G` project to walks of the merged graph. -/
lemma exists_walk_mergeGraph (hxy : x ≠ y) {u w : V} (p : G.Walk u w) :
    ∃ q : (G.mergeGraph x y).Walk (mergeMap x y u) (mergeMap x y w),
      ∀ v ∈ q.support, ∃ v' ∈ p.support, mergeMap x y v' = v := by
  induction p with
  | @nil u =>
    refine ⟨Walk.nil, fun v hv => ⟨u, by simp, ?_⟩⟩
    simp only [Walk.support_nil, List.mem_singleton] at hv
    exact hv.symm
  | @cons u u₁ w h p ih =>
    obtain ⟨q, hq⟩ := ih
    by_cases he : mergeMap x y u = mergeMap x y u₁
    · refine ⟨q.copy he.symm rfl, fun v hv => ?_⟩
      rw [Walk.support_copy] at hv
      obtain ⟨v', hv', rfl⟩ := hq v hv
      exact ⟨v', by simp [hv'], rfl⟩
    · refine ⟨Walk.cons (mergeGraph_adj_of_adj hxy h he) q, fun v hv => ?_⟩
      simp only [Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ⟨u, by simp, rfl⟩
      · obtain ⟨v', hv', rfl⟩ := hq v hv
        exact ⟨v', by simp [hv'], rfl⟩

/-- Walks of the merged graph lift to walks of `G`, from any preimage of the start. -/
lemma exists_walk_of_mergeGraph (hxy : G.Adj x y) {u w : V} (p : (G.mergeGraph x y).Walk u w)
    (u₀ : V) (hu₀ : mergeMap x y u₀ = u) :
    ∃ w₀, mergeMap x y w₀ = w ∧
      ∃ q : G.Walk u₀ w₀, ∀ v ∈ q.support, mergeMap x y v ∈ p.support := by
  induction p generalizing u₀ with
  | nil => exact ⟨u₀, hu₀, Walk.nil, fun v hv => by simp_all⟩
  | @cons u u' w h p ih =>
    obtain ⟨u₁, v₁, hu₁, hv₁, hadj⟩ := exists_adj_of_mergeGraph_adj h
    obtain ⟨r, hr⟩ := exists_walk_of_mergeMap_eq hxy (hu₀.trans hu₁.symm)
    obtain ⟨w₀, hw₀, q, hq⟩ := ih v₁ hv₁
    refine ⟨w₀, hw₀, r.append (Walk.cons hadj q), fun v hv => ?_⟩
    rcases (Walk.mem_support_append_iff _ _).1 hv with hv | hv
    · rw [hr v hv, hu₀]; simp
    · simp only [Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · rw [hu₁]; simp
      · exact List.mem_cons_of_mem _ (hq v hv)

omit [DecidableEq V] in
lemma ncard_edgeSet_mergeGraph_lt [Finite V] (hxy : G.Adj x y) :
    (G.mergeGraph x y).edgeSet.ncard < G.edgeSet.ncard := by
  classical
  have hsub : (G.mergeGraph x y).edgeSet ⊆
      Sym2.map (mergeMap x y) '' (G.edgeSet \ {s(x, y)}) := by
    intro e he
    induction e using Sym2.ind with
    | h u w =>
      rw [mem_edgeSet] at he
      obtain ⟨u₁, w₁, hu, hw, h⟩ := exists_adj_of_mergeGraph_adj he
      refine ⟨s(u₁, w₁), ⟨h, ?_⟩, by simp [hu, hw]⟩
      intro hs
      simp only [Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk] at hs
      apply he.1
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [← hu, ← hw, mergeMap_self, mergeMap_of_ne hxy.ne]
      · rw [← hu, ← hw, mergeMap_self, mergeMap_of_ne hxy.ne]
  calc (G.mergeGraph x y).edgeSet.ncard
      ≤ (Sym2.map (mergeMap x y) '' (G.edgeSet \ {s(x, y)})).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (G.edgeSet \ {s(x, y)}).ncard := Set.ncard_image_le (Set.toFinite _)
    _ < G.edgeSet.ncard := Set.ncard_sdiff_singleton_lt_of_mem hxy (Set.toFinite _)

end Merge

section MengerProof

variable {G : SimpleGraph V}

/-- Disjoint walks of the merged graph lift to disjoint walks of `G`. -/
lemma DisjointWalks.of_mergeGraph [DecidableEq V] {x y : V} (hxy : G.Adj x y) {A B : Finset V}
    {k : ℕ}
    (h : (G.mergeGraph x y).DisjointWalks (A.image (mergeMap x y)) (B.image (mergeMap x y)) k) :
    G.DisjointWalks A B k := by
  obtain ⟨a, b, p, hab, hp⟩ := h
  have key : ∀ i, ∃ a₀ b₀, a₀ ∈ A ∧ b₀ ∈ B ∧
      ∃ q : G.Walk a₀ b₀, ∀ v ∈ q.support, mergeMap x y v ∈ (p i).support := by
    intro i
    obtain ⟨a₀, ha₀, ha₀'⟩ := Finset.mem_image.1 (hab i).1
    obtain ⟨b₀, hb₀, hb₀'⟩ := Finset.mem_image.1 (hab i).2
    obtain ⟨w₀, hw₀, q, hq⟩ := exists_walk_of_mergeGraph hxy (p i) a₀ ha₀'
    obtain ⟨r, hr⟩ := exists_walk_of_mergeMap_eq hxy (hw₀.trans hb₀'.symm)
    refine ⟨a₀, b₀, ha₀, hb₀, q.append r, fun v hv => ?_⟩
    rcases (Walk.mem_support_append_iff _ _).1 hv with hv | hv
    · exact hq v hv
    · rw [hr v hv, hw₀]; exact (p i).end_mem_support
  choose a₀ b₀ ha₀ hb₀ q hq using key
  exact ⟨a₀, b₀, q, fun i => ⟨ha₀ i, hb₀ i⟩,
    fun i j hij v hvi hvj => hp i j hij _ (hq i v hvi) (hq j v hvj)⟩

/-- The preimage of a separator of the merged graph is a separator of `G`. -/
lemma separates_preimage_mergeMap [Fintype V] [DecidableEq V] {x y : V} (hxy : x ≠ y)
    {A B Y : Finset V}
    (hY : (G.mergeGraph x y).Separates (Y : Set V) (A.image (mergeMap x y))
      (B.image (mergeMap x y))) :
    G.Separates ((Finset.univ.filter fun v => mergeMap x y v ∈ Y : Finset V) : Set V) A B := by
  intro a ha b hb p
  obtain ⟨q, hq⟩ := exists_walk_mergeGraph hxy p
  obtain ⟨v, hv, hvY⟩ := hY _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ ha)) _
    (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb)) q
  obtain ⟨v', hv', rfl⟩ := hq v hv
  exact ⟨v', hv', by simpa using hvY⟩

/-- Base case of Menger's theorem: a graph without edges. -/
lemma disjointWalks_of_edgeSet_eq_empty (hG : G.edgeSet = ∅) {A B : Finset V} {k : ℕ}
    (h : ∀ X : Finset V, G.Separates (X : Set V) A B → k ≤ X.card) : G.DisjointWalks A B k := by
  classical
  have hsep : G.Separates ((A ∩ B : Finset V) : Set V) A B := by
    intro a ha b hb p
    cases p with
    | nil => exact ⟨a, by simp, by simp_all⟩
    | cons hadj _ =>
      have := (G.mem_edgeSet).2 hadj
      rw [hG] at this
      exact absurd this (Set.notMem_empty _)
  have hk := h _ hsep
  obtain ⟨g⟩ : Nonempty (Fin k ↪ (A ∩ B : Finset V)) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin, Fintype.card_coe]; exact hk)
  refine ⟨fun i => g i, fun i => g i, fun i => Walk.nil, fun i => ?_, ?_⟩
  · have := (g i).2
    rw [Finset.mem_inter] at this
    exact this
  · intro i j hij v hv hv'
    simp only [Walk.support_nil, List.mem_singleton] at hv hv'
    exact hij (g.injective (Subtype.ext (hv.symm.trans hv')))

/-- Induction step of Göring's proof of Menger's theorem. -/
lemma disjointWalks_step [Finite V] {x y : V} (hxy : G.Adj x y) {A B : Finset V} {k : ℕ}
    (h : ∀ X : Finset V, G.Separates (X : Set V) A B → k ≤ X.card)
    (ih : ∀ H : SimpleGraph V, H.edgeSet.ncard < G.edgeSet.ncard → ∀ (A B : Finset V) (k : ℕ),
      (∀ X : Finset V, H.Separates (X : Set V) A B → k ≤ X.card) → H.DisjointWalks A B k) :
    G.DisjointWalks A B k := by
  classical
  have := Fintype.ofFinite V
  by_contra hne
  have hY : ∃ Y : Finset V, (G.mergeGraph x y).Separates (Y : Set V) (A.image (mergeMap x y))
      (B.image (mergeMap x y)) ∧ Y.card < k := by
    by_contra hY
    push Not at hY
    exact hne (DisjointWalks.of_mergeGraph hxy (ih _ (ncard_edgeSet_mergeGraph_lt hxy) _ _ _ hY))
  obtain ⟨Y, hYsep, hYk⟩ := hY
  have hZsep := separates_preimage_mergeMap hxy.ne hYsep
  set Z := Finset.univ.filter fun v => mergeMap x y v ∈ Y with hZdef
  have hZk := h Z hZsep
  have hxY : x ∈ Y := by
    by_contra hxY
    have : Z ⊆ Y := by
      intro v hv
      simp only [hZdef, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      by_cases hvy : v = y
      · subst hvy; rw [mergeMap_self] at hv; exact absurd hv hxY
      · rwa [mergeMap_of_ne hvy] at hv
    exact absurd (hZk.trans (Finset.card_le_card this)) (not_le.2 hYk)
  have hxZ : x ∈ Z := by simp [hZdef, mergeMap_of_ne hxy.ne, hxY]
  have hyZ : y ∈ Z := by simp [hZdef, hxY]
  have hZk' : Z.card ≤ k := by
    have : Z ⊆ insert y Y := by
      intro v hv
      simp only [hZdef, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      by_cases hvy : v = y
      · simp [hvy]
      · rw [mergeMap_of_ne hvy] at hv; exact Finset.mem_insert_of_mem hv
    exact (Finset.card_le_card this).trans ((Finset.card_insert_le _ _).trans hYk)
  have hlt : (G.deleteEdges {s(x, y)}).edgeSet.ncard < G.edgeSet.ncard := by
    rw [edgeSet_deleteEdges]; exact Set.ncard_sdiff_singleton_lt_of_mem hxy (Set.toFinite _)
  have hA := ih _ hlt A Z k fun W hW =>
    h W (hZsep.of_deleteEdges (Finset.mem_coe.2 hxZ) (Finset.mem_coe.2 hyZ) hW)
  have hB := ih _ hlt B Z k fun W hW =>
    h W (hZsep.symm.of_deleteEdges (Finset.mem_coe.2 hxZ) (Finset.mem_coe.2 hyZ) hW).symm
  obtain ⟨a, z, p, haz, hpd, hp⟩ := (hA.mono (deleteEdges_le _)).exists_avoidsBeforeEnd
  obtain ⟨b, z', q, hbz, hqd, hq⟩ := (hB.mono (deleteEdges_le _)).exists_avoidsBeforeEnd
  exact hne (disjointWalks_of_glue hZsep hZk' a z p (fun i => (haz i).1) (fun i => (haz i).2)
    hpd hp b z' q (fun i => (hbz i).1) (fun i => (hbz i).2) hqd hq)

variable (G) in
/-- Menger's theorem for disjoint walks (internal version). -/
theorem disjointWalks_of_forall_separates [Finite V] (A B : Finset V) (k : ℕ)
    (h : ∀ X : Finset V, G.Separates (X : Set V) A B → k ≤ X.card) : G.DisjointWalks A B k := by
  obtain ⟨n, hn⟩ : ∃ n, G.edgeSet.ncard = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing G A B k with
  | _ n ih =>
    by_cases hG : G.edgeSet = ∅
    · exact disjointWalks_of_edgeSet_eq_empty hG h
    · obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.2 hG
      induction e using Sym2.ind with
      | h x y =>
        exact disjointWalks_step he h fun H hH A B k hk => ih _ (hn ▸ hH) H A B k hk rfl

end MengerProof

section Fan

variable {G : SimpleGraph V}

lemma Walk.exists_deleteIncidenceSet {v a b : V} (p : G.Walk a b) (hv : v ∉ p.support) :
    ∃ q : (G.deleteIncidenceSet v).Walk a b, q.support = p.support := by
  induction p with
  | nil => exact ⟨Walk.nil, rfl⟩
  | @cons a a₁ b h p ih =>
    simp only [Walk.support_cons, List.mem_cons, not_or] at hv
    obtain ⟨q, hq⟩ := ih hv.2
    have hadj : (G.deleteIncidenceSet v).Adj a a₁ :=
      deleteIncidenceSet_adj.2 ⟨h, Ne.symm hv.1, fun h' => hv.2 (h' ▸ p.start_mem_support)⟩
    exact ⟨Walk.cons hadj q, by simp [hq]⟩

lemma Walk.notMem_support_deleteIncidenceSet {v a b : V}
    (p : (G.deleteIncidenceSet v).Walk a b) (ha : a ≠ v) : v ∉ p.support := by
  induction p with
  | nil => simpa using Ne.symm ha
  | cons h p ih =>
    simp only [Walk.support_cons, List.mem_cons, not_or]
    exact ⟨Ne.symm ha, ih (deleteIncidenceSet_adj.1 h).2.2⟩

/-- A path from `v` to `u ≠ v` leaves `v` through a neighbour `n`, and continues from `n` in the
graph without the edges at `v`. -/
lemma Walk.IsPath.exists_tail_deleteIncidenceSet {v u : V} {p : G.Walk v u} (hp : p.IsPath)
    (hvu : v ≠ u) : ∃ n, G.Adj v n ∧ ∃ q : (G.deleteIncidenceSet v).Walk n u,
      ∀ x ∈ q.support, x ∈ p.support ∧ x ≠ v := by
  cases p with
  | nil => exact absurd rfl hvu
  | @cons _ n _ h p =>
    rw [Walk.cons_isPath_iff] at hp
    obtain ⟨q, hq⟩ := p.exists_deleteIncidenceSet hp.2
    refine ⟨n, h, q, fun x hx => ?_⟩
    rw [hq] at hx
    exact ⟨List.mem_cons_of_mem _ hx, fun h => hp.2 (h ▸ hx)⟩

/-- Disjoint walks can be shortcut to disjoint paths. -/
lemma DisjointWalks.exists_paths {A B : Finset V} {k : ℕ} (h : G.DisjointWalks A B k) :
    ∃ (a b : Fin k → V) (p : ∀ i, G.Walk (a i) (b i)), (∀ i, a i ∈ A ∧ b i ∈ B ∧ (p i).IsPath) ∧
      ∀ i j, i ≠ j → ∀ v ∈ (p i).support, v ∉ (p j).support := by
  classical
  obtain ⟨a, b, p, hab, hp⟩ := h
  exact ⟨a, b, fun i => (p i).bypass, fun i => ⟨(hab i).1, (hab i).2, (p i).bypass_isPath⟩,
    fun i j hij x hx hx' => hp i j hij x ((p i).support_bypass_subset_support hx)
      ((p j).support_bypass_subset_support hx')⟩

variable (G)

/-- Menger's theorem, set version: if every `A`–`B` separator has at least `k` vertices, there
are `k` pairwise vertex-disjoint `A`–`B` paths. -/
theorem menger [Finite V] (A B : Finset V) (k : ℕ)
    (h : ∀ X : Finset V, G.Separates (X : Set V) A B → k ≤ X.card) :
    ∃ P : Fin k → Σ a b : V, G.Walk a b,
      (∀ i, (P i).1 ∈ A ∧ (P i).2.1 ∈ B ∧ (P i).2.2.IsPath) ∧
      ∀ i j, i ≠ j → ∀ x ∈ (P i).2.2.support, x ∉ (P j).2.2.support := by
  obtain ⟨a, b, p, hab, hp⟩ := (G.disjointWalks_of_forall_separates A B k h).exists_paths
  exact ⟨fun i => ⟨a i, b i, p i⟩, hab, hp⟩

/-- Fan lemma: if no set of fewer than `k` vertices other than `v` cuts `v` off from `U`, there are
`k` paths from `v` to distinct vertices of `U`, pairwise sharing only `v`. -/
theorem fan [Finite V] (v : V) (U : Finset V) (hv : v ∉ U) (k : ℕ)
    (h : ∀ X : Finset V, v ∉ X → X.card < k → ∃ u ∈ U, G.ReachableAvoiding (X : Set V) v u) :
    ∃ P : Fin k → Σ u : V, G.Walk v u,
      (∀ i, (P i).1 ∈ U ∧ (P i).2.IsPath) ∧
      ∀ i j, i ≠ j → ∀ x ∈ (P i).2.support, x ∈ (P j).2.support → x = v := by
  classical
  have := Fintype.ofFinite V
  let A : Finset V := Finset.univ.filter (G.Adj v)
  have hsep : ∀ X : Finset V, (G.deleteIncidenceSet v).Separates (X : Set V) A U →
      k ≤ X.card := by
    intro X hX
    by_contra hlt
    push Not at hlt
    obtain ⟨u, hu, p, hp⟩ := h (X.erase v) (by simp) ((Finset.card_erase_le).trans_lt hlt)
    have hvu : v ≠ u := fun h => hv (h ▸ hu)
    obtain ⟨n, hn, q, hq⟩ := p.bypass_isPath.exists_tail_deleteIncidenceSet hvu
    obtain ⟨x, hx, hxX⟩ := hX n (by simp [A, hn]) u hu q
    obtain ⟨hx₁, hx₂⟩ := hq x hx
    exact hp x (p.support_bypass_subset_support hx₁) (by simpa [hx₂] using hxX)
  obtain ⟨a, b, p, hab, hp⟩ :=
    ((G.deleteIncidenceSet v).disjointWalks_of_forall_separates A U k hsep).exists_paths
  have hadj : ∀ i, G.Adj v (a i) := fun i => by simpa [A] using (hab i).1
  refine ⟨fun i => ⟨b i, Walk.cons (hadj i) ((p i).mapLe (G.deleteIncidenceSet_le v))⟩,
    fun i => ⟨(hab i).2.1, ?_⟩, ?_⟩
  · rw [Walk.cons_isPath_iff]
    refine ⟨(hab i).2.2.mapLe _, ?_⟩
    rw [Walk.support_mapLe_eq_support]
    exact (p i).notMem_support_deleteIncidenceSet (hadj i).ne.symm
  · intro i j hij x hxi hxj
    simp only [Walk.support_cons, Walk.support_mapLe_eq_support, List.mem_cons] at hxi hxj
    rcases hxi with hxi | hxi
    · exact hxi
    rcases hxj with hxj | hxj
    · exact hxj
    exact absurd hxj (hp i j hij x hxi)

variable {G}

/-- Fan lemma for `k`-connected graphs. -/
theorem IsVertexConnected.fan [Fintype V] {k : ℕ} (hG : G.IsVertexConnected k) (v : V)
    (U : Finset V) (hv : v ∉ U) (hU : k ≤ U.card) :
    ∃ P : Fin k → Σ u : V, G.Walk v u,
      (∀ i, (P i).1 ∈ U ∧ (P i).2.IsPath) ∧
      ∀ i j, i ≠ j → ∀ x ∈ (P i).2.support, x ∈ (P j).2.support → x = v := by
  refine G.fan v U hv k fun X hvX hX => ?_
  obtain ⟨u, huU, huX⟩ : ∃ u ∈ U, u ∉ X := by
    by_contra hc
    push Not at hc
    exact absurd (hU.trans (Finset.card_le_card hc)) (not_le.2 hX)
  exact ⟨u, huU, hG.2 X hX v u hvX huX⟩

end Fan

end SimpleGraph
