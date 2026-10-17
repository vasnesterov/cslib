/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Foundations.Relation.RelatesInSteps
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Card

/-!
# Reachability, bounded walks and source components of digraphs

Mathlib's `Digraph` has no path API. Distributed-computing papers on directed networks need
reachability, reachability inside the subgraph obtained by deleting a set of (faulty) nodes, walks
of bounded length, strong connectivity, and the source components of the condensation. This file
provides them on top of `Relation.ReflTransGen` and CSLib's bounded-step relations
`Relation.RelatesInSteps` (walks of length exactly `n`) and `Relation.RelatesWithinSteps` (walks of
length at most `n`).

## Main definitions

* `Digraph.deleteVerts G X`: delete the vertices of `X` (they stay, without arcs).
* `Digraph.Reachable G u v`: there is a directed walk from `u` to `v`.
* `Digraph.StronglyConnected G`: every vertex reaches every vertex.
* `Digraph.ReachableAvoiding G X u v`: there is a directed walk from `u` to `v` all of whose
  vertices (endpoints included) lie outside `X`; the reach set `reach_v(X)` of the fault-tolerant
  consensus literature is `{u | G.ReachableAvoiding X u v}`.
* `Digraph.IsStronglyConnectedOn G S`, `Digraph.IsStronglyConnectedComponent G S`,
  `Digraph.IsSourceComponent G S`: the induced subgraph on `S` is strongly connected; `S` is a
  maximal such set; `S` is a strongly connected component without incoming arcs.

## Main results

* `Relation.ReflTransGen.relatesWithinSteps_card_sub_one`, `Digraph.Reachable.relatesWithinSteps`:
  in a finite type, every reachable vertex is reachable within `|V| - 1` steps.
* `Relation.RelatesInSteps.exists_le_first_visit` (in `Cslib.Foundations.Relation.RelatesInSteps`):
  a walk can be cut at the first visit of its target.
* `Digraph.ReachableAvoiding.exists_isChainFromTo`: reachability avoiding `X` is witnessed by a
  simple path (a duplicate-free list of vertices) outside `X`.
* `Digraph.isSourceComponent_iff`: `S` is a source component iff `S` is the set of ancestors of a
  vertex `r` that is reachable from all of its ancestors.
* `Digraph.exists_isSourceComponent_subset`: in a finite digraph every vertex has a source
  component among its ancestors.
-/

@[expose] public section

open Relation

namespace Digraph

variable {V : Type*} {G H : Digraph V} {X Y S T : Set V} {u v w : V}

/-! ### Vertex deletion -/

/-- `G.deleteVerts X`: remove all arcs incident to a vertex of `X` (the vertices stay, isolated). -/
def deleteVerts (G : Digraph V) (X : Set V) : Digraph V where
  Adj u v := G.Adj u v ∧ u ∉ X ∧ v ∉ X

/-- Arcs of `G.deleteVerts X` are the arcs of `G` with both ends outside `X`. -/
@[simp] theorem deleteVerts_adj : (G.deleteVerts X).Adj u v ↔ G.Adj u v ∧ u ∉ X ∧ v ∉ X :=
  Iff.rfl

/-- Deleting vertices gives a subgraph. -/
theorem deleteVerts_le (G : Digraph V) (X : Set V) : G.deleteVerts X ≤ G := fun _ _ h => h.1

/-- Deleting more vertices gives a smaller digraph. -/
theorem deleteVerts_anti (h : X ⊆ Y) : G.deleteVerts Y ≤ G.deleteVerts X :=
  fun _ _ e => ⟨e.1, fun hu => e.2.1 (h hu), fun hv => e.2.2 (h hv)⟩

/-- Deleting no vertices changes nothing. -/
@[simp] theorem deleteVerts_empty (G : Digraph V) : G.deleteVerts ∅ = G := by ext; simp

/-! ### Reachability -/

/-- `G.Reachable u v`: there is a directed walk (possibly empty) from `u` to `v`. -/
def Reachable (G : Digraph V) (u v : V) : Prop := ReflTransGen G.Adj u v

/-- Every vertex reaches itself. -/
@[refl] theorem Reachable.refl (u : V) : G.Reachable u u := ReflTransGen.refl

/-- Every vertex reaches itself (implicit version). -/
theorem Reachable.rfl : G.Reachable u u := ReflTransGen.refl

/-- An arc is a walk. -/
theorem Adj.reachable (h : G.Adj u v) : G.Reachable u v := ReflTransGen.single h

/-- Reachability is transitive. -/
@[trans] theorem Reachable.trans (h₁ : G.Reachable u v) (h₂ : G.Reachable v w) :
    G.Reachable u w :=
  ReflTransGen.trans h₁ h₂

/-- Extend a walk by a final arc. -/
theorem Reachable.tail (h : G.Reachable u v) (e : G.Adj v w) : G.Reachable u w :=
  ReflTransGen.tail h e

/-- Extend a walk by an initial arc. -/
theorem Reachable.head (e : G.Adj u v) (h : G.Reachable v w) : G.Reachable u w :=
  ReflTransGen.head e h

/-- Reachability is monotone in the digraph. -/
theorem Reachable.mono (hGH : G ≤ H) (h : G.Reachable u v) : H.Reachable u v :=
  ReflTransGen.mono (fun _ _ e => hGH e) _ _ h

/-- Reachability is reachability within some number of steps. -/
theorem reachable_iff_exists_relatesWithinSteps :
    G.Reachable u v ↔ ∃ n, RelatesWithinSteps G.Adj u v n :=
  reflTransGen_iff_exists_relatesWithinSteps

/-- In a finite digraph every reachable vertex is reachable within `|V| - 1` steps. -/
theorem Reachable.relatesWithinSteps [Fintype V] (h : G.Reachable u v) :
    RelatesWithinSteps G.Adj u v (Fintype.card V - 1) :=
  ReflTransGen.relatesWithinSteps_card_sub_one h

/-- Reachability is witnessed by a simple path, given as a duplicate-free list of vertices. -/
theorem Reachable.exists_isChainFromTo (h : G.Reachable u v) :
    ∃ l : List V, l.IsChainFromTo G.Adj u v ∧ l.Nodup :=
  ReflTransGen.exists_isChainFromTo_nodup h

/-- Every vertex reaches every vertex. -/
def StronglyConnected (G : Digraph V) : Prop := ∀ u v, G.Reachable u v

/-! ### Reachability avoiding a set of vertices -/

/-- `G.ReachableAvoiding X u v`: there is a directed walk from `u` to `v` all of whose vertices,
endpoints included, lie outside `X` (a walk in `G.deleteVerts X` starting outside `X`). -/
def ReachableAvoiding (G : Digraph V) (X : Set V) (u v : V) : Prop :=
  u ∉ X ∧ (G.deleteVerts X).Reachable u v

namespace ReachableAvoiding

/-- A vertex outside `X` reaches itself avoiding `X`. -/
theorem refl (h : u ∉ X) : G.ReachableAvoiding X u u := ⟨h, .rfl⟩

/-- The start of a walk avoiding `X` is outside `X`. -/
theorem notMem_left (h : G.ReachableAvoiding X u v) : u ∉ X := h.1

/-- The end of a walk avoiding `X` is outside `X`. -/
theorem notMem_right (h : G.ReachableAvoiding X u v) : v ∉ X := by
  obtain ⟨hu, h⟩ := h
  induction h with
  | refl => exact hu
  | tail _ e _ => exact e.2.2

/-- Reachability avoiding `X` implies reachability. -/
theorem reachable (h : G.ReachableAvoiding X u v) : G.Reachable u v :=
  h.2.mono (deleteVerts_le G X)

/-- Reachability avoiding `X` is transitive. -/
@[trans] theorem trans (h₁ : G.ReachableAvoiding X u v) (h₂ : G.ReachableAvoiding X v w) :
    G.ReachableAvoiding X u w :=
  ⟨h₁.1, h₁.2.trans h₂.2⟩

/-- Extend a walk avoiding `X` by a final arc to a vertex outside `X`. -/
theorem tail (h : G.ReachableAvoiding X u v) (e : G.Adj v w) (hw : w ∉ X) :
    G.ReachableAvoiding X u w :=
  ⟨h.1, h.2.tail ⟨e, h.notMem_right, hw⟩⟩

/-- Extend a walk avoiding `X` by an initial arc from a vertex outside `X`. -/
theorem head (e : G.Adj u v) (hu : u ∉ X) (h : G.ReachableAvoiding X v w) :
    G.ReachableAvoiding X u w :=
  ⟨hu, h.2.head ⟨e, hu, h.1⟩⟩

/-- Avoiding a larger set implies avoiding a smaller one. -/
theorem anti (h : G.ReachableAvoiding Y u v) (hXY : X ⊆ Y) : G.ReachableAvoiding X u v :=
  ⟨fun hu => h.1 (hXY hu), h.2.mono (deleteVerts_anti hXY)⟩

/-- If every arc into `L` from a vertex outside `X` starts in `L`, then every vertex reaching `L`
while avoiding `X` lies in `L`. -/
theorem mem_of_closed {L : Set V} (hL : ∀ a b, G.Adj a b → a ∉ X → b ∈ L → a ∈ L)
    (h : G.ReachableAvoiding X u v) (hv : v ∈ L) : u ∈ L := by
  obtain ⟨-, h⟩ := h
  induction h using ReflTransGen.head_induction_on with
  | refl => exact hv
  | head e _ ih => exact hL _ _ e.1 e.2.1 ih

/-- Reachability avoiding `X` is witnessed by a simple path outside `X`. -/
theorem exists_isChainFromTo (h : G.ReachableAvoiding X u v) :
    ∃ l : List V, l.IsChainFromTo G.Adj u v ∧ l.Nodup ∧ ∀ x ∈ l, x ∉ X := by
  obtain ⟨l, hl, hnd⟩ := Reachable.exists_isChainFromTo h.2
  refine ⟨l, ⟨hl.isChain.imp fun _ _ e => e.1, hl.ne_nil, hl.head_eq, hl.getLast_eq⟩, hnd,
    fun x hx => ?_⟩
  have hx' : (G.deleteVerts X).Reachable u x := hl.reflTransGen_of_mem hx
  exact (ReachableAvoiding.notMem_right ⟨h.1, hx'⟩ :)

end ReachableAvoiding

/-- Avoiding the empty set is plain reachability. -/
@[simp] theorem reachableAvoiding_empty : G.ReachableAvoiding ∅ u v ↔ G.Reachable u v := by
  simp [ReachableAvoiding]

/-! ### Strongly connected components and source components -/

/-- The subgraph induced by `S` is strongly connected: any two vertices of `S` are joined by a
walk inside `S`. -/
def IsStronglyConnectedOn (G : Digraph V) (S : Set V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, G.ReachableAvoiding Sᶜ u v

/-- `S` is a strongly connected component: non-empty, strongly connected and maximal. -/
def IsStronglyConnectedComponent (G : Digraph V) (S : Set V) : Prop :=
  S.Nonempty ∧ G.IsStronglyConnectedOn S ∧ ∀ T, S ⊆ T → G.IsStronglyConnectedOn T → T = S

/-- A source component: a strongly connected component without arcs entering it from outside. -/
def IsSourceComponent (G : Digraph V) (S : Set V) : Prop :=
  G.IsStronglyConnectedComponent S ∧ ∀ v ∈ S, ∀ u, G.Adj u v → u ∈ S

/-- Predecessor-closed sets contain all ancestors of their members. -/
theorem mem_of_reachable_of_closed (hS : ∀ v ∈ S, ∀ u, G.Adj u v → u ∈ S)
    (h : G.Reachable u v) (hv : v ∈ S) : u ∈ S := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hab _ ih => exact hS _ ih _ hab

/-- In a predecessor-closed set `S`, walks into `S` stay inside `S`. -/
theorem reachableAvoiding_compl_of_closed (hS : ∀ v ∈ S, ∀ u, G.Adj u v → u ∈ S)
    (h : G.Reachable u v) (hv : v ∈ S) : G.ReachableAvoiding Sᶜ u v := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact .refl (by simpa using hv)
  | head hab hbc ih =>
    have hb := mem_of_reachable_of_closed hS hbc hv
    exact ih.head hab (by simpa using hS _ hb _ hab)

/-- Source components are the sets of ancestors `{x | x ⇝ r}` of a vertex `r` that is reachable
from each of its ancestors. -/
theorem isSourceComponent_iff :
    G.IsSourceComponent S ↔
      ∃ r, S = {x | G.Reachable x r} ∧ ∀ x, G.Reachable x r → G.Reachable r x := by
  constructor
  · rintro ⟨⟨⟨r, hr⟩, hsc, -⟩, hcl⟩
    have hS : S = {x | G.Reachable x r} := by
      ext x
      exact ⟨fun hx => (hsc x hx r hr).reachable,
        fun hx => mem_of_reachable_of_closed hcl hx hr⟩
    exact ⟨r, hS, fun x hx => (hsc r hr x (hS ▸ hx)).reachable⟩
  · rintro ⟨r, rfl, hr⟩
    have hcl : ∀ v ∈ {x | G.Reachable x r}, ∀ u, G.Adj u v → u ∈ {x | G.Reachable x r} :=
      fun v hv u e => e.reachable.trans hv
    refine ⟨⟨⟨r, .rfl⟩, fun u hu v hv =>
      reachableAvoiding_compl_of_closed hcl ((hu : G.Reachable u r).trans (hr v hv)) hv,
      fun T hST hT => ?_⟩, hcl⟩
    exact Set.Subset.antisymm (fun t ht => (hT t ht r (hST .rfl)).reachable) hST

namespace IsSourceComponent

/-- A source component has no incoming arcs from outside. -/
theorem closed (hS : G.IsSourceComponent S) : ∀ v ∈ S, ∀ u, G.Adj u v → u ∈ S := hS.2

/-- A source component is non-empty. -/
theorem nonempty (hS : G.IsSourceComponent S) : S.Nonempty := hS.1.1

/-- A source component is the set of ancestors of any of its vertices. -/
theorem eq_setOf_reachable (hS : G.IsSourceComponent S) (hr : v ∈ S) :
    S = {x | G.Reachable x v} := by
  ext x
  exact ⟨fun hx => (hS.1.2.1 x hx v hr).reachable,
    fun hx => mem_of_reachable_of_closed hS.closed hx hr⟩

/-- Any two vertices of a source component reach each other. -/
theorem reachable (hS : G.IsSourceComponent S) (hu : u ∈ S) (hv : v ∈ S) : G.Reachable u v :=
  (hS.1.2.1 u hu v hv).reachable

/-- Two source components sharing a vertex are equal. -/
theorem eq_of_mem (hS : G.IsSourceComponent S) (hT : G.IsSourceComponent T) (hvS : v ∈ S)
    (hvT : v ∈ T) : S = T := by
  rw [hS.eq_setOf_reachable hvS, hT.eq_setOf_reachable hvT]

/-- Distinct source components are disjoint. -/
theorem disjoint (hS : G.IsSourceComponent S) (hT : G.IsSourceComponent T) (hne : S ≠ T) :
    Disjoint S T :=
  Set.disjoint_left.mpr fun _ hS' hT' => hne (hS.eq_of_mem hT hS' hT')

end IsSourceComponent

/-- In a finite digraph every vertex has a source component among its ancestors. -/
theorem exists_isSourceComponent_subset [Finite V] (v : V) :
    ∃ S, G.IsSourceComponent S ∧ S ⊆ {x | G.Reachable x v} := by
  induction h : Set.ncard {x | G.Reachable x v} using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hall : ∀ x, G.Reachable x v → G.Reachable v x
    · exact ⟨_, isSourceComponent_iff.mpr ⟨v, rfl, hall⟩, le_rfl⟩
    · push Not at hall
      obtain ⟨x, hxv, hvx⟩ := hall
      have hsub : {y | G.Reachable y x} ⊂ {y | G.Reachable y v} :=
        Set.ssubset_iff_subset_ne.mpr ⟨fun y hy => (hy : G.Reachable y x).trans hxv,
          fun heq => hvx (by
            have : v ∈ {y | G.Reachable y v} := Reachable.rfl
            rwa [← heq] at this)⟩
      obtain ⟨S, hS, hSx⟩ := ih _ (h ▸ Set.ncard_lt_ncard hsub (Set.toFinite _)) x rfl
      exact ⟨S, hS, hSx.trans hsub.subset⟩

/-- A non-empty finite digraph has a source component. -/
theorem exists_isSourceComponent [Finite V] [Nonempty V] : ∃ S, G.IsSourceComponent S :=
  let ⟨S, hS, _⟩ := exists_isSourceComponent_subset (G := G) (Classical.arbitrary V)
  ⟨S, hS⟩

/-- If `G` has a unique source component `S`, every vertex of `S` is an ancestor of every
vertex. -/
theorem subset_setOf_reachable_of_unique [Finite V]
    (huniq : ∀ T, G.IsSourceComponent T → T = S) (v : V) : S ⊆ {x | G.Reachable x v} := by
  obtain ⟨T, hT, hTv⟩ := exists_isSourceComponent_subset (G := G) v
  exact huniq T hT ▸ hTv

end Digraph
