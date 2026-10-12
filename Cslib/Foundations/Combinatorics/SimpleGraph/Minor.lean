/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Tactic.FinCases

/-!
# Graph minors and minor density

`H` is a minor of `G` if there is a *minor model* (a.k.a. branch sets): a family of pairwise
disjoint vertex sets of `G`, one per vertex of `H`, each inducing a connected subgraph of `G`, such
that adjacent vertices of `H` have adjacent branch sets. (Equivalently, `H` is obtained from `G` by
deleting vertices and edges and contracting edges.)

The *minor density* of `G` is the maximum of `|E(H)| / |V(H)|` over all minors `H` of `G`.

## Main definitions

* `SimpleGraph.MinorModel H G`: a minor model of `H` in `G`.
* `SimpleGraph.IsMinor H G`: `H` is a minor of `G`.
* `SimpleGraph.MinorDensityLE G δ`: every finite minor `H` of `G` has `|E(H)| ≤ δ |V(H)|`.
* `SimpleGraph.minorDensity G`: the minor density `δ(G)`.
* `SimpleGraph.MinorModel.refl`, `MinorModel.ofCopy`, `MinorModel.compCopy`, `MinorModel.trans`:
  constructions of minor models.

## Main results

* `SimpleGraph.IsMinor.refl`, `IsMinor.of_le`, `IsMinor.of_isContained`, `IsMinor.of_iso`,
  `IsMinor.trans`: being a minor is a preorder containing the subgraph relation.
* `SimpleGraph.IsMinor.card_le`, `IsMinor.finite`: minors of finite graphs are not larger.
* `SimpleGraph.MinorDensityLE.le`: the density bound for minors on vertex types in any universe.
* `SimpleGraph.MinorDensityLE.mono` (= `IsMinor.minorDensityLE`), `MinorDensityLE.of_le`:
  monotonicity in the graph (w.r.t. minors) and in `δ`.
* `SimpleGraph.MinorDensityLE.nonneg`, `MinorDensityLE.half_le`: `δ ≥ 0`, resp. `δ ≥ 1/2` for a
  graph with a vertex, resp. an edge.
* `SimpleGraph.MinorDensityLE.bipartite_card_le`: counting edges of a bipartite minor given by
  branch sets.
* For finite `G`: `minorDensityLE_minorDensity`, `minorDensity_le_iff` (`δ(G) ≤ δ ↔
  G.MinorDensityLE δ` for `δ ≥ 0`), `exists_isMinor_minorDensity_eq` (the supremum is attained),
  `IsMinor.minorDensity_le`, `minorDensity_nonneg`, `minorDensity_le_card`.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*}

/-- A minor model of `H` in `G`: pairwise disjoint branch sets inducing connected subgraphs, with
an edge of `G` between the branch sets of any two adjacent vertices of `H`. -/
structure MinorModel (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch set of a vertex of `H`. -/
  branch : W → Set V
  connected : ∀ w, (G.induce (branch w)).Connected
  disjoint : Pairwise fun a b => Disjoint (branch a) (branch b)
  adj : ∀ a b, H.Adj a b → ∃ x ∈ branch a, ∃ y ∈ branch b, G.Adj x y

/-- `H` is a minor of `G`. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop := Nonempty (MinorModel H G)

/-- Every finite minor `H` of `G` (on a vertex type in `Type`) has at most `δ · |V(H)|` edges,
i.e. the minor density of `G` is at most `δ`. See `MinorDensityLE.le` for minors on vertex types
in arbitrary universes. -/
def MinorDensityLE (G : SimpleGraph V) (δ : ℝ) : Prop :=
  ∀ (W : Type) [Finite W] (H : SimpleGraph W), IsMinor H G →
    (H.edgeSet.ncard : ℝ) ≤ δ * Nat.card W

/-- The minor density `δ(G) = max {|E(H)| / |V(H)| : H a minor of G}` (for finite `G`). -/
noncomputable def minorDensity (G : SimpleGraph V) : ℝ :=
  sSup {x | ∃ (W : Type) (_ : Finite W) (H : SimpleGraph W), IsMinor H G ∧
    x = H.edgeSet.ncard / Nat.card W}

namespace MinorModel

variable {U : Type*} {G : SimpleGraph V} {G' : SimpleGraph U} {H : SimpleGraph W}

/-- Branch sets of a minor model are nonempty. -/
theorem branch_nonempty (M : MinorModel H G) (w : W) : (M.branch w).Nonempty := by
  obtain ⟨⟨x, hx⟩⟩ := (M.connected w).nonempty
  exact ⟨x, hx⟩

/-- Precomposing a minor model of `H` with a copy of `H'` in `H` gives a minor model of `H'`. -/
def compCopy {W' : Type*} {H' : SimpleGraph W'} (M : MinorModel H G) (f : Copy H' H) :
    MinorModel H' G where
  branch w := M.branch (f w)
  connected w := M.connected (f w)
  disjoint _ _ h := M.disjoint fun h' => h (f.injective h')
  adj _ _ h := M.adj _ _ (f.toHom.map_adj h)

/-- The trivial minor model of `G` in itself, with singleton branch sets. -/
def refl (G : SimpleGraph V) : MinorModel G G where
  branch v := {v}
  connected v := by rw [induce_singleton_eq_top]; exact connected_top
  disjoint _ _ h := Set.disjoint_singleton.2 h
  adj a b h := ⟨a, rfl, b, rfl, h⟩

/-- A copy of `H` in `G` (i.e. `H` is isomorphic to a subgraph of `G`) gives a minor model. -/
def ofCopy (f : Copy H G) : MinorModel H G := (refl G).compCopy f

/-- If the vertices of a connected set `S` of `G'` are replaced by connected sets `B u` of `G`
with `G`-edges between `B u` and `B u'` whenever `u ~ u'` in `G'`, the union stays connected. -/
private theorem reachable_of_reachable {S : Set U} (B : U → Set V) {T : Set V}
    (hT : ∀ u ∈ S, B u ⊆ T) (hB : ∀ u ∈ S, (G.induce (B u)).Connected)
    (hadj : ∀ u ∈ S, ∀ u' ∈ S, G'.Adj u u' → ∃ x ∈ B u, ∃ y ∈ B u', G.Adj x y)
    {a b : S} (hab : (G'.induce S).Reachable a b) {x y : V} (hx : x ∈ B a) (hy : y ∈ B b) :
    (G.induce T).Reachable ⟨x, hT a a.2 hx⟩ ⟨y, hT b b.2 hy⟩ := by
  have base : ∀ (a : S) {x y : V} (hx : x ∈ B a) (hy : y ∈ B a),
      (G.induce T).Reachable ⟨x, hT a a.2 hx⟩ ⟨y, hT a a.2 hy⟩ := fun a x y hx hy =>
    ((hB a a.2).preconnected ⟨x, hx⟩ ⟨y, hy⟩).map (induceHomOfLE G (hT a a.2)).toHom
  obtain ⟨p⟩ := hab
  induction p generalizing x with
  | nil => exact base _ hx hy
  | @cons a c b h p ih =>
    obtain ⟨x', hx', y', hy', hxy⟩ := hadj a a.2 c c.2 h
    exact (base a hx hx').trans
      ((show (G.induce T).Adj ⟨x', hT a a.2 hx'⟩ ⟨y', hT c c.2 hy'⟩ from hxy).reachable.trans
        (ih hy' hy))

/-- Composition of minor models: a minor of a minor is a minor. The branch set of `w` is the
union of the branch sets (in `G`) of the vertices in the branch set (in `G'`) of `w`. -/
def trans (M₁ : MinorModel H G') (M₂ : MinorModel G' G) : MinorModel H G where
  branch w := ⋃ u ∈ M₁.branch w, M₂.branch u
  connected w := by
    rw [connected_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hx⟩ ⟨y, hy⟩
      simp only [Set.mem_iUnion] at hx hy
      obtain ⟨u, hu, hxu⟩ := hx
      obtain ⟨u', hu', hyu'⟩ := hy
      exact reachable_of_reachable (S := M₁.branch w) M₂.branch
        (fun u hu => Set.subset_biUnion_of_mem (u := M₂.branch) hu) (fun u _ => M₂.connected u)
        (fun u _ u' _ h => M₂.adj u u' h)
        ((M₁.connected w).preconnected ⟨u, hu⟩ ⟨u', hu'⟩) hxu hyu'
    · obtain ⟨u, hu⟩ := M₁.branch_nonempty w
      obtain ⟨x, hx⟩ := M₂.branch_nonempty u
      exact ⟨⟨x, Set.mem_biUnion hu hx⟩⟩
  disjoint a b h := by
    simp only [Set.disjoint_iUnion₂_left, Set.disjoint_iUnion₂_right]
    intro u hu u' hu'
    refine M₂.disjoint ?_
    rintro rfl
    first
    | exact Set.disjoint_left.1 (M₁.disjoint h) hu hu'
    | exact Set.disjoint_left.1 (M₁.disjoint h) hu' hu
  adj a b h := by
    obtain ⟨u, hu, u', hu', huu'⟩ := M₁.adj a b h
    obtain ⟨x, hx, y, hy, hxy⟩ := M₂.adj u u' huu'
    exact ⟨x, Set.mem_biUnion hu hx, y, Set.mem_biUnion hu' hy, hxy⟩

/-- Choosing a vertex in each branch set is injective. -/
theorem injective_some (M : MinorModel H G) :
    Function.Injective fun w => (M.branch_nonempty w).some := by
  intro a b hab
  by_contra h
  refine Set.disjoint_left.1 (M.disjoint h) (M.branch_nonempty a).some_mem ?_
  simp only at hab
  rw [hab]
  exact (M.branch_nonempty b).some_mem

/-- A minor of a finite graph has at most as many vertices. -/
theorem card_le [Finite V] (M : MinorModel H G) : Nat.card W ≤ Nat.card V :=
  Nat.card_le_card_of_injective _ M.injective_some

/-- A minor of a finite graph is finite. -/
theorem finite [Finite V] (M : MinorModel H G) : Finite W :=
  Finite.of_injective _ M.injective_some

end MinorModel

namespace IsMinor

variable {U : Type*} {G : SimpleGraph V} {G' : SimpleGraph U} {H : SimpleGraph W}

/-- Every graph is a minor of itself. -/
@[refl] theorem refl (G : SimpleGraph V) : IsMinor G G := ⟨MinorModel.refl G⟩

/-- A graph contained in `G` (a copy of a subgraph of `G`) is a minor of `G`. -/
theorem of_isContained (h : H ⊑ G) : IsMinor H G := let ⟨f⟩ := h; ⟨MinorModel.ofCopy f⟩

/-- A graph isomorphic to `G` is a minor of `G`. -/
theorem of_iso (e : H ≃g G) : IsMinor H G := ⟨MinorModel.ofCopy e.toCopy⟩

/-- A subgraph of `G` is a minor of `G`. -/
theorem of_le {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) : IsMinor G₁ G₂ :=
  ⟨MinorModel.ofCopy ⟨⟨id, fun hab => h hab⟩, Function.injective_id⟩⟩

/-- Being a minor is transitive. -/
theorem trans (h₁ : IsMinor H G') (h₂ : IsMinor G' G) : IsMinor H G :=
  let ⟨M₁⟩ := h₁; let ⟨M₂⟩ := h₂; ⟨M₁.trans M₂⟩

/-- A minor of a finite graph has at most as many vertices. -/
theorem card_le [Finite V] (h : IsMinor H G) : Nat.card W ≤ Nat.card V :=
  let ⟨M⟩ := h; M.card_le

/-- A minor of a finite graph is finite. -/
theorem finite [Finite V] (h : IsMinor H G) : Finite W := let ⟨M⟩ := h; M.finite

end IsMinor

/-- The number of edges of a finite graph is at most `(|V| choose 2)`. -/
theorem ncard_edgeSet_le_choose_two [Finite V] (G : SimpleGraph V) :
    G.edgeSet.ncard ≤ (Nat.card V).choose 2 := by
  classical
  have := Fintype.ofFinite V
  rw [Set.ncard_eq_toFinset_card', Nat.card_eq_fintype_card]
  convert G.card_edgeFinset_le_card_choose_two
  simp [edgeFinset]

/-- The number of edges of a finite graph is at most `|V|²`. -/
theorem ncard_edgeSet_le_card_mul_card [Finite V] (G : SimpleGraph V) :
    G.edgeSet.ncard ≤ Nat.card V * Nat.card V := by
  refine G.ncard_edgeSet_le_choose_two.trans ?_
  rw [Nat.choose_two_right]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- Isomorphic graphs have the same number of edges. -/
theorem Iso.ncard_edgeSet_eq {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    G.edgeSet.ncard = H.edgeSet.ncard :=
  Set.ncard_congr' e.mapEdgeSet

namespace MinorDensityLE

variable {U : Type*} {G : SimpleGraph V} {G' : SimpleGraph U} {δ δ' : ℝ}

/-- `MinorDensityLE` for minors on vertex types in arbitrary universes. -/
theorem le (hG : G.MinorDensityLE δ) {W : Type*} [Finite W] (H : SimpleGraph W)
    (h : IsMinor H G) : (H.edgeSet.ncard : ℝ) ≤ δ * Nat.card W := by
  obtain ⟨M⟩ := h
  let e := Finite.equivFin W
  let iso := Iso.map e H
  have := hG _ _ ⟨M.compCopy iso.symm.toCopy⟩
  rwa [← iso.ncard_edgeSet_eq, Nat.card_fin] at this

/-- Density bounds are monotone in `δ`. -/
theorem of_le (hG : G.MinorDensityLE δ) (hδ : δ ≤ δ') : G.MinorDensityLE δ' :=
  fun W _ H h => (hG W H h).trans (by gcongr)

/-- A minor of `G` inherits every minor-density bound of `G`. -/
theorem mono (hG : G.MinorDensityLE δ) (h : IsMinor G' G) : G'.MinorDensityLE δ :=
  fun W _ H hH => hG W H (hH.trans h)

/-- A graph with a vertex has minor density `≥ 0` (single-vertex minor). -/
theorem nonneg (hG : G.MinorDensityLE δ) [Nonempty V] : 0 ≤ δ := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have := hG Unit ⊥ (.of_isContained ⟨⟨⟨fun _ => v, fun h => absurd h (by simp)⟩,
    fun _ _ _ => rfl⟩⟩)
  simpa using this

/-- A graph with an edge has minor density `≥ 1/2` (`K₂` minor). -/
theorem half_le (hG : G.MinorDensityLE δ) {u v : V} (huv : G.Adj u v) : 1 / 2 ≤ δ := by
  let f : Fin 2 → V := ![u, v]
  have hf : ∀ i j, (⊤ : SimpleGraph (Fin 2)).Adj i j → G.Adj (f i) (f j) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f, huv.symm]
  have hinj : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f, huv.ne, huv.ne.symm]
  have := hG (Fin 2) ⊤ (.of_isContained ⟨⟨⟨f, hf _ _⟩, hinj⟩⟩)
  have h1 : (⊤ : SimpleGraph (Fin 2)).edgeSet.ncard = 1 := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two]
    rfl
  rw [h1, Nat.card_fin] at this
  push_cast at this
  linarith

/-- **Bipartite minors.** Given branch sets `f a` (`a ∈ A`) and `g b` (`b ∈ B`) that are pairwise
disjoint and induce connected subgraphs, and a relation `r` such that `r a b` implies an edge
between `f a` and `g b`, the number of related pairs is at most `δ (|A| + |B|)`. -/
theorem bipartite_card_le (hG : G.MinorDensityLE δ) {α β : Type*} (A : Finset α) (B : Finset β)
    (f : α → Set V) (g : β → Set V) (r : α → β → Prop) [∀ a b, Decidable (r a b)]
    (hf : ∀ a ∈ A, (G.induce (f a)).Connected) (hg : ∀ b ∈ B, (G.induce (g b)).Connected)
    (hff : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → Disjoint (f a) (f a'))
    (hgg : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → Disjoint (g b) (g b'))
    (hfg : ∀ a ∈ A, ∀ b ∈ B, Disjoint (f a) (g b))
    (hr : ∀ a ∈ A, ∀ b ∈ B, r a b → ∃ x ∈ f a, ∃ y ∈ g b, G.Adj x y) :
    (((A ×ˢ B).filter fun p => r p.1 p.2).card : ℝ) ≤ δ * (A.card + B.card) := by
  -- The bipartite graph `H` on `A ⊕ B` with `inl a ~ inr b ↔ r a b`.
  let R : A ⊕ B → A ⊕ B → Prop
    | .inl a, .inr b => r a b
    | .inr b, .inl a => r a b
    | _, _ => False
  let H : SimpleGraph (A ⊕ B) :=
    { Adj := R
      symm := ⟨by rintro (a | b) (a' | b') h <;> exact h⟩
      loopless := ⟨by rintro (a | b) h <;> exact h⟩ }
  let M : MinorModel H G :=
    { branch := Sum.elim (fun a => f a) (fun b => g b)
      connected := by rintro (a | b); exacts [hf a a.2, hg b b.2]
      disjoint := by
        rintro (a | b) (a' | b') h
        · exact hff a a.2 a' a'.2 fun h' => h (by rw [Subtype.ext h'])
        · exact hfg a a.2 b' b'.2
        · exact (hfg a' a'.2 b b.2).symm
        · exact hgg b b.2 b' b'.2 fun h' => h (by rw [Subtype.ext h'])
      adj := by
        rintro (a | b) (a' | b') h
        · exact h.elim
        · exact hr a a.2 b' b'.2 h
        · obtain ⟨x, hx, y, hy, hxy⟩ := hr a' a'.2 b b.2 h
          exact ⟨y, hy, x, hx, hxy.symm⟩
        · exact h.elim }
  have hE : H.edgeSet = (fun p : A × B => s(Sum.inl p.1, Sum.inr p.2)) '' {p | r p.1 p.2} := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      rcases x with a | b <;> rcases y with a' | b' <;> simp [H, R]
  have hinj : Function.Injective fun p : A × B => (s(Sum.inl p.1, Sum.inr p.2) : Sym2 (A ⊕ B)) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simpa using h
  have hcard : H.edgeSet.ncard = ((A ×ˢ B).filter fun p => r p.1 p.2).card := by
    rw [hE, Set.ncard_image_of_injective _ hinj, ← Set.ncard_coe_finset]
    refine Set.ncard_congr (fun p _ => (p.1.1, p.2.1)) ?_ ?_ ?_
    · rintro ⟨a, b⟩ h
      simpa using h
    · rintro ⟨a, b⟩ ⟨a', b'⟩ _ _ h
      simp only [Prod.mk.injEq] at h
      rw [Subtype.ext h.1, Subtype.ext h.2]
    · rintro ⟨a, b⟩ h
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at h
      exact ⟨(⟨a, h.1.1⟩, ⟨b, h.1.2⟩), h.2, rfl⟩
  have := hG.le H ⟨M⟩
  rwa [hcard, Nat.card_sum, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_coe, Fintype.card_coe, Nat.cast_add] at this

end MinorDensityLE

/-- A minor `H` of `G` inherits every minor-density bound of `G`. -/
theorem IsMinor.minorDensityLE {U : Type*} {G : SimpleGraph V} {H : SimpleGraph U} {δ : ℝ}
    (h : IsMinor H G) (hG : G.MinorDensityLE δ) : H.MinorDensityLE δ :=
  hG.mono h

section minorDensity

variable {G : SimpleGraph V} {δ : ℝ}

/-- The edge-to-vertex ratio `|E(H)| / |V(H)|` of a finite minor is at most `|V(G)|`. -/
private theorem ratio_le_card [Finite V] {W : Type*} [Finite W] {H : SimpleGraph W}
    (h : IsMinor H G) : (H.edgeSet.ncard : ℝ) / Nat.card W ≤ Nat.card V := by
  rcases (Nat.card W).eq_zero_or_pos with hW | hW
  · rw [hW, Nat.cast_zero, div_zero]
    positivity
  rw [div_le_iff₀ (by exact_mod_cast hW)]
  have h₁ := H.ncard_edgeSet_le_card_mul_card
  have h₂ := h.card_le
  have : (H.edgeSet.ncard : ℝ) ≤ Nat.card W * Nat.card W := by exact_mod_cast h₁
  have : (Nat.card W : ℝ) ≤ Nat.card V := by exact_mod_cast h₂
  nlinarith

/-- The empty graph is a minor of every graph, so `0` belongs to the set defining
`minorDensity`. -/
private theorem zero_mem_minorDensity_set :
    (0 : ℝ) ∈ {x : ℝ | ∃ (W : Type) (_ : Finite W) (H : SimpleGraph W), IsMinor H G ∧
      x = H.edgeSet.ncard / Nat.card W} :=
  ⟨Empty, inferInstance, ⊥, ⟨⟨Empty.elim, fun w => w.elim, fun w => w.elim, fun w => w.elim⟩⟩,
    by simp⟩

private theorem bddAbove_minorDensity_set [Finite V] :
    BddAbove {x : ℝ | ∃ (W : Type) (_ : Finite W) (H : SimpleGraph W), IsMinor H G ∧
      x = H.edgeSet.ncard / Nat.card W} := by
  refine ⟨Nat.card V, ?_⟩
  rintro x ⟨W, _, H, h, rfl⟩
  exact ratio_le_card h

/-- The minor density is nonnegative. -/
theorem minorDensity_nonneg : 0 ≤ G.minorDensity := by
  refine Real.sSup_nonneg fun x ⟨W, _, H, _, hx⟩ => hx ▸ by positivity

/-- The minor density of a finite graph is at most its number of vertices. -/
theorem minorDensity_le_card [Finite V] : G.minorDensity ≤ Nat.card V :=
  csSup_le ⟨0, zero_mem_minorDensity_set⟩ fun _ ⟨_, _, _, h, hx⟩ => hx ▸ ratio_le_card h

/-- The edge-to-vertex ratio of a finite minor of a finite graph `G` is at most `δ(G)`. -/
theorem IsMinor.div_le_minorDensity [Finite V] {W : Type*} [Finite W] {H : SimpleGraph W}
    (h : IsMinor H G) : (H.edgeSet.ncard : ℝ) / Nat.card W ≤ G.minorDensity := by
  let e := Finite.equivFin W
  let iso := Iso.map e H
  have hH := (IsMinor.of_iso iso.symm).trans h
  have := le_csSup bddAbove_minorDensity_set ⟨_, inferInstance, _, hH, rfl⟩
  rwa [← iso.ncard_edgeSet_eq, Nat.card_fin] at this

/-- A finite graph satisfies the minor-density bound `δ(G)`. -/
theorem minorDensityLE_minorDensity [Finite V] : G.MinorDensityLE G.minorDensity := by
  intro W _ H h
  rcases (Nat.card W).eq_zero_or_pos with hW | hW
  · have : IsEmpty W := (Nat.card_eq_zero.1 hW).resolve_right (not_infinite_iff_finite.2 ‹_›)
    simp [Set.eq_empty_of_isEmpty]
  rw [← div_le_iff₀ (by exact_mod_cast hW)]
  exact h.div_le_minorDensity

/-- For a finite graph and `δ ≥ 0`: `δ(G) ≤ δ` iff every minor `H` has `|E(H)| ≤ δ |V(H)|`. -/
theorem minorDensity_le_iff [Finite V] (hδ : 0 ≤ δ) :
    G.minorDensity ≤ δ ↔ G.MinorDensityLE δ := by
  refine ⟨minorDensityLE_minorDensity.of_le, fun hG => ?_⟩
  refine csSup_le ⟨0, zero_mem_minorDensity_set⟩ ?_
  rintro x ⟨W, _, H, h, rfl⟩
  rcases (Nat.card W).eq_zero_or_pos with hW | hW
  · simpa [hW] using hδ
  rw [div_le_iff₀ (by exact_mod_cast hW)]
  exact hG W H h

/-- Minor density is monotone under taking minors. -/
theorem IsMinor.minorDensity_le [Finite V] {U : Type*} {H : SimpleGraph U} (h : IsMinor H G) :
    H.minorDensity ≤ G.minorDensity :=
  have := h.finite
  (minorDensity_le_iff minorDensity_nonneg).2 (minorDensityLE_minorDensity.mono h)

/-- The supremum defining the minor density of a finite graph is attained by some minor. -/
theorem exists_isMinor_minorDensity_eq [Finite V] :
    ∃ (W : Type) (_ : Finite W) (H : SimpleGraph W), IsMinor H G ∧
      G.minorDensity = H.edgeSet.ncard / Nat.card W := by
  set N := Nat.card V
  have hfin : {x : ℝ | ∃ (W : Type) (_ : Finite W) (H : SimpleGraph W), IsMinor H G ∧
      x = H.edgeSet.ncard / Nat.card W}.Finite := by
    refine ((Set.finite_Iic (N * N)).prod (Set.finite_Iic N)).image
      (fun p : ℕ × ℕ => (p.1 : ℝ) / p.2) |>.subset ?_
    rintro x ⟨W, _, H, h, rfl⟩
    exact ⟨(H.edgeSet.ncard, Nat.card W),
      ⟨H.ncard_edgeSet_le_card_mul_card.trans (Nat.mul_le_mul h.card_le h.card_le), h.card_le⟩,
      rfl⟩
  exact Set.Nonempty.csSup_mem ⟨0, zero_mem_minorDensity_set⟩ hfin

end minorDensity

end SimpleGraph
