/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Foundations.Combinatorics.SimpleGraph.Ball
public import Cslib.Foundations.Data.Nat.TimeRec
public import Cslib.Computability.Distributed.Local.LocallyIterative
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Locally-iterative algorithms: neighbour states, identifiers, runs

In the locally-iterative (SET-LOCAL) model a node only sees the **set** `nbrColors G c v` of
its neighbours' states. Many LOCAL algorithms are run in this model by storing the node's
identifier in its state: if `idOf (c u) = u` for every `u`, the set of neighbour states determines
the neighbours themselves, and a node can count, sum over, or address individual neighbours. This
file provides that identifier API, and identifies runs with time-dependent iterations
(`Nat.timeRec`).

## Main definitions

* `Cslib.LocallyIterative.pickId idOf d N u`: the state with identifier `u` in the set `N`
  (default `d`); how a node addresses its neighbour `u`.

## Main statements

* `exists_mem_nbrColors`, `forall_mem_nbrColors`: quantifiers over neighbour states.
* `insert_nbrColors`: own state and neighbour states are the image of the closed neighbourhood.
* With identifiers (`hc : ∀ u, idOf (c u) = u`): `exists_mem_nbrColors_id` (a neighbour state with
  identifier `u` exists iff `u` is a neighbour), `pickId_nbrColors`, `ncard_nbrColors_filter`
  (counting neighbour states = counting neighbours), `finsum_nbrColors` (summing over neighbour
  states = summing over neighbours).
* `Algorithm.run_eq_timeRec`: a run is the time-dependent iteration of the global round map.
* `Algorithm.run_ofStep`: runs of round-independent algorithms are iterates;
  `Algorithm.run_semiconj`: simulation of a global map by a round-independent algorithm.

## Implementation notes

CSLib's `Algorithm.run_add` and `Algorithm.run_comap` are instances of `Nat.timeRec_add` and
`Nat.timeRec_semiconj`: after `simp only [run_eq_timeRec, Nat.timeRec_add]` the first is `rfl`, and
the second is `(Nat.timeRec_semiconj _ _ h t).symm` with `h` the one-round computation
`simp [comap, hed, nbrColors_comp, Set.image_image]`. They are kept with their direct inductive
proofs in `Cslib.Computability.Distributed.Local.LocallyIterative`, which does not depend on
`Nat.timeRec`.
-/

@[expose] public section

namespace Cslib.LocallyIterative

open SimpleGraph Finset

variable {V C M : Type*} {G : SimpleGraph V} {c : V → C} {u v : V}

/-! ### Quantifiers over neighbour states -/

/-- Some neighbour state satisfies `P` iff some neighbour's state does. -/
theorem exists_mem_nbrColors {P : C → Prop} :
    (∃ x ∈ nbrColors G c v, P x) ↔ ∃ u, G.Adj v u ∧ P (c u) :=
  Set.exists_mem_image

/-- All neighbour states satisfy `P` iff all neighbours' states do. -/
theorem forall_mem_nbrColors {P : C → Prop} :
    (∀ x ∈ nbrColors G c v, P x) ↔ ∀ u, G.Adj v u → P (c u) :=
  Set.forall_mem_image

/-- A node's own state together with its neighbours' states: the image of its closed
neighbourhood. -/
theorem insert_nbrColors (c : V → C) (v : V) :
    insert (c v) (nbrColors G c v) = c '' G.closedNeighborSet v :=
  (Set.image_insert_eq ..).symm

/-! ### States carrying identifiers

Throughout, `idOf : C → V` reads the identifier stored in a state, and the hypothesis
`hc : ∀ u, idOf (c u) = u` says that every node stores its own identifier. -/

section Identifiers

variable (idOf : C → V)

/-- A neighbour state with identifier `u` satisfying `P` exists iff `u` is a neighbour whose
state satisfies `P`. -/
theorem exists_mem_nbrColors_id (hc : ∀ u, idOf (c u) = u) {P : C → Prop} :
    (∃ x ∈ nbrColors G c v, idOf x = u ∧ P x) ↔ G.Adj v u ∧ P (c u) := by
  rw [exists_mem_nbrColors]
  constructor
  · rintro ⟨w, hw, hid, hP⟩
    rw [hc] at hid
    exact hid ▸ ⟨hw, hP⟩
  · rintro ⟨h, hP⟩
    exact ⟨u, h, hc u, hP⟩

/-- A neighbour state with identifier `u` exists iff `u` is a neighbour. -/
theorem exists_mem_nbrColors_id_eq (hc : ∀ u, idOf (c u) = u) :
    (∃ x ∈ nbrColors G c v, idOf x = u) ↔ G.Adj v u := by
  simpa using exists_mem_nbrColors_id idOf hc (P := fun _ => True)

open scoped Classical in
/-- The state with identifier `u` in the set of states `N` (an arbitrary one if there are
several; the default `d` if there is none): how a node reads the state of its neighbour `u`. -/
noncomputable def pickId (d : C) (N : Set C) (u : V) : C :=
  if h : ∃ x ∈ N, idOf x = u then Classical.choose h else d

/-- Reading the state of the neighbour `u` from the set of neighbour states. -/
theorem pickId_nbrColors (hc : ∀ u, idOf (c u) = u) (d : C) (h : G.Adj v u) :
    pickId idOf d (nbrColors G c v) u = c u := by
  have hex : ∃ x ∈ nbrColors G c v, idOf x = u := (exists_mem_nbrColors_id_eq idOf hc).2 h
  simp only [pickId, hex, ↓reduceDIte]
  obtain ⟨⟨w, -, hw⟩, hid⟩ := Classical.choose_spec hex
  rw [← hw, hc] at hid
  rw [← hw, hid]

open scoped Classical in
/-- Counting neighbour states with identifier in a set `s` of neighbours is counting the
neighbours in `s`. -/
theorem ncard_nbrColors_filter (hc : ∀ u, idOf (c u) = u) (s : Finset V)
    (hs : ∀ u ∈ s, G.Adj v u) (P : C → Prop) :
    {x ∈ nbrColors G c v | idOf x ∈ s ∧ P x}.ncard = #{u ∈ s | P (c u)} := by
  have hinj : Function.Injective c := Function.LeftInverse.injective hc
  have : {x ∈ nbrColors G c v | idOf x ∈ s ∧ P x} = c '' ↑({u ∈ s | P (c u)}) := by
    ext x
    simp only [Set.mem_ofPred_eq, nbrColors, Set.mem_image, mem_neighborSet, coe_filter]
    constructor
    · rintro ⟨⟨u, -, rfl⟩, hid, hP⟩
      rw [hc] at hid
      exact ⟨u, ⟨hid, hP⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hP⟩, rfl⟩
      exact ⟨⟨u, hs u hu, rfl⟩, by rw [hc]; exact hu, hP⟩
  rw [this, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset]

/-- Summing over neighbour states is summing over neighbours. -/
theorem finsum_nbrColors [AddCommMonoid M] [Fintype (G.neighborSet v)]
    (hc : ∀ u, idOf (c u) = u) (f : C → M) :
    ∑ᶠ x ∈ nbrColors G c v, f x = ∑ u ∈ G.neighborFinset v, f (c u) := by
  rw [nbrColors, finsum_mem_image (Function.LeftInverse.injective hc).injOn,
    finsum_mem_eq_toFinset_sum]
  rfl

end Identifiers

/-! ### Runs as time-dependent iterations -/

namespace Algorithm

variable (G)

/-- A run of a locally-iterative algorithm is the time-dependent iteration of its global round
map. -/
theorem run_eq_timeRec (A : Algorithm C) (c₀ : V → C) (t : ℕ) :
    A.run G c₀ t = Nat.timeRec (fun t c v => A.step t (c v) (nbrColors G c v)) c₀ t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih]; rfl

/-- Runs of a round-independent algorithm are iterates of its global round map. -/
theorem run_ofStep (f : C → Set C → C) (c₀ : V → C) (t : ℕ) :
    (ofStep f).run G c₀ t = (fun c v => f (c v) (nbrColors G c v))^[t] c₀ := by
  rw [run_eq_timeRec, ← Nat.timeRec_const]; rfl

/-- **Simulation.** If a round of the round-independent algorithm `ofStep f` on encoded
configurations `e s` computes the encoding of `F s`, then its runs from `e s₀` encode the iterates
of `F`. -/
theorem run_semiconj {σ : Type*} (f : C → Set C → C) {F : σ → σ} {e : σ → V → C}
    (h : ∀ s, (fun v => f (e s v) (nbrColors G (e s) v)) = e (F s)) (s₀ : σ) (t : ℕ) :
    (ofStep f).run G (e s₀) t = e (F^[t] s₀) := by
  rw [run_ofStep, ← Nat.timeRec_const, ← Nat.timeRec_const]
  exact (Nat.timeRec_semiconj _ _ (fun _ s => (h s).symm) t).symm

end Algorithm

end Cslib.LocallyIterative
