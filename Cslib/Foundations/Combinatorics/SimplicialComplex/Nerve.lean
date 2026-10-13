/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Nerves of set families and simplicial maps

Mathlib has abstract simplicial complexes (`PreAbstractSimplicialComplex`,
`AbstractSimplicialComplex`) but neither nerves nor simplicial maps.

## Main definitions

* `PreAbstractSimplicialComplex.nerve U`: the nerve of a family of sets `U : V → Set P`: a nonempty
  finite set of vertices is a face iff the corresponding sets have a common point.
* `PreAbstractSimplicialComplex.IsSimplicialMap K L f`: `f` maps faces of `K` to faces of `L`.

## Main results

* `isSimplicialMap_nerve_iff`: for nerves, `f` is simplicial iff every common point of a face is
  witnessed by a common point of the image face.
-/

@[expose] public section

namespace PreAbstractSimplicialComplex

variable {V W P Q : Type*}

/-- The nerve of a family of sets: a nonempty finite set of indices is a face iff the sets it
indexes have a common point. -/
def nerve (U : V → Set P) : PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ ∃ p, ∀ v ∈ s, p ∈ U v}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, fun t hts ht => ⟨ht, ?_⟩⟩
    obtain ⟨p, hp⟩ := hs.2
    exact ⟨p, fun v hv => hp v (hts hv)⟩

theorem mem_nerve {U : V → Set P} {s : Finset V} :
    s ∈ nerve U ↔ s.Nonempty ∧ ∃ p, ∀ v ∈ s, p ∈ U v := Iff.rfl

/-- `f` is a simplicial map from `K` to `L`: the image of every face is a face. -/
def IsSimplicialMap [DecidableEq W] (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (f : V → W) : Prop :=
  ∀ s ∈ K, s.image f ∈ L

/-- A map between nerves is simplicial iff every face (nonempty finite set of vertices with a
common point) is sent to a finite set of vertices with a common point. -/
theorem isSimplicialMap_nerve_iff [DecidableEq W] (U : V → Set P) (U' : W → Set Q) (f : V → W) :
    IsSimplicialMap (nerve U) (nerve U') f ↔
      ∀ s : Finset V, s.Nonempty → (∃ p, ∀ v ∈ s, p ∈ U v) → ∃ q, ∀ v ∈ s, q ∈ U' (f v) := by
  constructor
  · intro h s hs ⟨p, hp⟩
    obtain ⟨-, q, hq⟩ := h s ⟨hs, p, hp⟩
    exact ⟨q, fun v hv => hq (f v) (Finset.mem_image_of_mem f hv)⟩
  · intro h s ⟨hs, hp⟩
    obtain ⟨q, hq⟩ := h s hs hp
    refine ⟨hs.image f, q, ?_⟩
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    exact hq v hv

end PreAbstractSimplicialComplex
