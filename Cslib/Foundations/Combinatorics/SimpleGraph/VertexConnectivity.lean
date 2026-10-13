/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Data.Fintype.Card

/-!
# Vertex connectivity of simple graphs

Mathlib has edge connectivity (`SimpleGraph.IsEdgeConnected`) but no vertex connectivity. This
file sets up the basic notions used to state Menger's theorem.

## Main definitions

* `G.ReachableAvoiding X u v`: some walk from `u` to `v` has no vertex (endpoints included) in `X`.
* `G.Separates X A B`: every walk from a vertex of `A` to a vertex of `B` meets `X`.
* `G.IsVertexConnected k`: `G` is `k`-(vertex-)connected in the sense of West: `G` has more than
  `k` vertices and removing fewer than `k` vertices leaves it connected.

## References

* D. B. West, *Introduction to Graph Theory*, 2nd ed., Prentice Hall, 2001.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- `u` and `v` are joined by a walk all of whose vertices (endpoints included) lie outside `X`. -/
def ReachableAvoiding (X : Set V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∉ X

/-- `X` separates `A` from `B`: every walk from a vertex of `A` to a vertex of `B` has a vertex
in `X` (endpoints included). -/
def Separates (X A B : Set V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b, ∃ x ∈ p.support, x ∈ X

/-- `G` is `k`-(vertex-)connected (West): it has more than `k` vertices, and removing fewer than
`k` vertices does not disconnect it. -/
def IsVertexConnected [Fintype V] (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ X : Finset V, X.card < k → ∀ u v, u ∉ X → v ∉ X → G.ReachableAvoiding (X : Set V) u v

variable {G}

lemma IsVertexConnected.mono [Fintype V] {k l : ℕ} (h : G.IsVertexConnected k) (hlk : l ≤ k) :
    G.IsVertexConnected l :=
  ⟨lt_of_le_of_lt hlk h.1, fun X hX => h.2 X (lt_of_lt_of_le hX hlk)⟩

lemma ReachableAvoiding.mono {X Y : Set V} {u v : V} (h : G.ReachableAvoiding Y u v)
    (hXY : X ⊆ Y) : G.ReachableAvoiding X u v := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun x hx hxX => hp x hx (hXY hxX)⟩

lemma ReachableAvoiding.symm {X : Set V} {u v : V} (h : G.ReachableAvoiding X u v) :
    G.ReachableAvoiding X v u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, fun x hx => hp x (by simpa using hx)⟩

lemma ReachableAvoiding.trans {X : Set V} {u v w : V} (h₁ : G.ReachableAvoiding X u v)
    (h₂ : G.ReachableAvoiding X v w) : G.ReachableAvoiding X u w := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  refine ⟨p.append q, fun x hx => ?_⟩
  rcases (Walk.mem_support_append_iff p q).1 hx with hx | hx
  exacts [hp x hx, hq x hx]

lemma Separates.not_reachableAvoiding {X A B : Set V} (h : G.Separates X A B) {a b : V}
    (ha : a ∈ A) (hb : b ∈ B) : ¬ G.ReachableAvoiding X a b := by
  rintro ⟨p, hp⟩
  obtain ⟨x, hx, hxX⟩ := h a ha b hb p
  exact hp x hx hxX

lemma Separates.symm {X A B : Set V} (h : G.Separates X A B) : G.Separates X B A := by
  intro b hb a ha p
  obtain ⟨x, hx, hxX⟩ := h a ha b hb p.reverse
  exact ⟨x, by simpa using hx, hxX⟩

end SimpleGraph
