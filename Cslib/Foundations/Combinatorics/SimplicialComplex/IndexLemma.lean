/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The combinatorial index lemma (Sperner-type parity/counting lemma)

We prove the generalized combinatorial *index lemma* of Rajsbaum and Raventós-Pujol
(PODC 2022, Theorem 3.1), a generalization of the index lemma in Henle,
*A Combinatorial Introduction to Topology*.

## Setting

A 2-dimensional complex is given by a finite family of *oriented triangles*
`tri : T → V × V × V`; the oriented triangle `(a, b, c)` induces the directed edges
`a → b`, `b → c`, `c → a` (`dirEdges`). An undirected edge `{u, w}` is a *boundary edge*
(`IsBoundary`) if it lies in exactly one triangle (counted with multiplicity). The complex is
*oriented* (`IsOriented`) if on every non-boundary edge the induced orientations cancel in pairs:
the directed edge `u → w` is induced exactly as often as `w → u`.

Given a colouring `c : V → Fin 3`,
* the *index* (`index`) counts the boundary edges coloured `{0, 1}`: `+1` if the orientation
  induced by its triangle reads `0 → 1`, `-1` if it reads `1 → 0`;
* the *content* (`content`) counts the trichromatic triangles: `+1` if the orientation reads
  `0, 1, 2` cyclically, `-1` if it reads `0, 2, 1` cyclically.

## Main result

* `Cslib.Simplicial.index_eq_content`: for an oriented complex, `index = content`.

## Proof

Let `S` be the sum of the edge values over all directed-edge occurrences. Per triangle, the sum of
the three edge values is the triangle value (a finite check over the 27 colour triples), so
`S = content`. The difference `S - index` is the sum over non-boundary occurrences, which regroups
as `∑ e, edgeCount e * g e` with `g` antisymmetric under swapping the endpoints; by the orientation
condition `edgeCount` is symmetric on non-boundary edges, so this sum equals its own negative.
-/

@[expose] public section

namespace Cslib.Simplicial

variable {V T : Type*} [DecidableEq V] [Fintype T]

/-- The three directed edges of an oriented triangle `(a, b, c)` (orientation a → b → c → a). -/
def dirEdges (x : V × V × V) : List (V × V) := [(x.1, x.2.1), (x.2.1, x.2.2), (x.2.2, x.1)]

/-- Number of times the directed edge `e` is induced by the oriented triangles `tri`. -/
def edgeCount (tri : T → V × V × V) (e : V × V) : ℕ := ∑ t, (dirEdges (tri t)).count e

/-- `{u, w}` is a boundary edge: it lies in exactly one triangle. -/
def IsBoundary (tri : T → V × V × V) (u w : V) : Prop :=
  edgeCount tri (u, w) + edgeCount tri (w, u) = 1

instance (tri : T → V × V × V) (u w : V) : Decidable (IsBoundary tri u w) :=
  inferInstanceAs (Decidable (_ = _))

/-- Orientation condition: on every non-boundary edge the induced orientations cancel in pairs. -/
def IsOriented (tri : T → V × V × V) : Prop :=
  ∀ u w, ¬ IsBoundary tri u w → edgeCount tri (u, w) = edgeCount tri (w, u)

/-- Contribution of a directed edge to the index: +1 for 0→1, −1 for 1→0. -/
def edgeVal (c : V → Fin 3) (e : V × V) : ℤ :=
  if c e.1 = 0 ∧ c e.2 = 1 then 1 else if c e.1 = 1 ∧ c e.2 = 0 then -1 else 0

/-- Value of a triangle whose vertices, read along its orientation, have colours `i, j, k`:
`+1` for a cyclic rotation of `0, 1, 2`, `-1` for a cyclic rotation of `0, 2, 1`, else `0`. -/
def triValCol (i j k : Fin 3) : ℤ :=
  if (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 1 ∧ j = 2 ∧ k = 0) ∨ (i = 2 ∧ j = 0 ∧ k = 1) then 1
  else if (i = 0 ∧ j = 2 ∧ k = 1) ∨ (i = 2 ∧ j = 1 ∧ k = 0) ∨ (i = 1 ∧ j = 0 ∧ k = 2) then -1
  else 0

/-- Contribution of an oriented triangle to the content: +1 if its colours read 0,1,2 cyclically
in its orientation, −1 if they read 0,2,1 cyclically, 0 if it is not trichromatic. -/
def triVal (c : V → Fin 3) (x : V × V × V) : ℤ := triValCol (c x.1) (c x.2.1) (c x.2.2)

/-- Content: signed number of trichromatic triangles. -/
def content (tri : T → V × V × V) (c : V → Fin 3) : ℤ := ∑ t, triVal c (tri t)

/-- Index: sum over boundary directed edges (each boundary edge appears exactly once, with the
orientation induced by its unique triangle). -/
def index (tri : T → V × V × V) (c : V → Fin 3) : ℤ :=
  ∑ t, (((dirEdges (tri t)).filter (fun e => decide (IsBoundary tri e.1 e.2))).map (edgeVal c)).sum

/-! ### Auxiliary lemmas -/

/-- Colour-level version of `edgeVal`. -/
private def edgeValCol (i j : Fin 3) : ℤ :=
  if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0

omit [DecidableEq V] in
private lemma edgeVal_eq (c : V → Fin 3) (e : V × V) :
    edgeVal c e = edgeValCol (c e.1) (c e.2) := rfl

omit [DecidableEq V] in
lemma edgeVal_swap (c : V → Fin 3) (e : V × V) : edgeVal c e.swap = - edgeVal c e := by
  rw [edgeVal_eq, edgeVal_eq, Prod.fst_swap, Prod.snd_swap]
  generalize c e.1 = i
  generalize c e.2 = j
  revert i j
  decide

omit [DecidableEq V] in
/-- Per triangle, the edge values along its orientation sum to the triangle value. -/
lemma sum_dirEdges_edgeVal (c : V → Fin 3) (x : V × V × V) :
    ((dirEdges x).map (edgeVal c)).sum = triVal c x := by
  obtain ⟨a, b, d⟩ := x
  simp only [dirEdges, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, edgeVal_eq,
    triVal, add_zero]
  generalize c a = i
  generalize c b = j
  generalize c d = k
  revert i j k
  decide

lemma isBoundary_comm (tri : T → V × V × V) (u w : V) :
    IsBoundary tri u w ↔ IsBoundary tri w u := by
  unfold IsBoundary
  rw [add_comm]

private lemma sum_map_filter_add {α : Type*} (l : List α) (p : α → Bool) (f : α → ℤ) :
    ((l.filter p).map f).sum + (l.map (fun a => if p a then 0 else f a)).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a
    · simp [h, ← ih, add_assoc]
    · simp [h, ← ih]
      ring

/-- Regrouping a sum over directed-edge occurrences by directed edge. -/
lemma sum_map_eq_sum_edgeCount (tri : T → V × V × V) (φ : V × V → ℤ) (E : Finset (V × V))
    (hE : ∀ t, ∀ e ∈ dirEdges (tri t), e ∈ E) :
    ∑ t, ((dirEdges (tri t)).map φ).sum = ∑ e ∈ E, (edgeCount tri e : ℤ) * φ e := by
  have key : ∀ t, ((dirEdges (tri t)).map φ).sum =
      ∑ e ∈ E, ((dirEdges (tri t)).count e : ℤ) * φ e := by
    intro t
    rw [Finset.sum_list_map_count]
    simp only [nsmul_eq_mul]
    apply Finset.sum_subset
    · intro e he
      exact hE t e (List.mem_toFinset.mp he)
    · intro e _ he
      rw [List.count_eq_zero_of_not_mem (by simpa using he)]
      simp
  simp_rw [key]
  rw [Finset.sum_comm]
  simp [edgeCount, Finset.sum_mul]

/-! ### The index lemma -/

/-- Theorem 3.1 of [Rajsbaum, Raventós-Pujol, *A Combinatorial Topology Approach to Arrow's
Impossibility Theorem*, PODC 2022] (generalized index lemma): in an oriented 2-dimensional complex
coloured with 3 colours, the index equals the content. -/
theorem index_eq_content (tri : T → V × V × V) (h : IsOriented tri) (c : V → Fin 3) :
    index tri c = content tri c := by
  -- the non-boundary part of the edge value
  set g : V × V → ℤ := fun e => if decide (IsBoundary tri e.1 e.2) then 0 else edgeVal c e
    with hg
  -- a finite set of directed edges containing all occurring ones, closed under swapping
  set A : Finset (V × V) := Finset.univ.biUnion (fun t => (dirEdges (tri t)).toFinset) with hA
  set E : Finset (V × V) := A ∪ A.image Prod.swap with hE
  have hmemE : ∀ t, ∀ e ∈ dirEdges (tri t), e ∈ E := by
    intro t e he
    refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, ?_⟩)
    exact List.mem_toFinset.mpr he
  have hswapE : ∀ e ∈ E, e.swap ∈ E := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
    · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
      rw [Prod.swap_swap]
      exact Finset.mem_union_left _ he'
  -- antisymmetry of the summand
  have hanti : ∀ e : V × V,
      (edgeCount tri e.swap : ℤ) * g e.swap = -((edgeCount tri e : ℤ) * g e) := by
    rintro ⟨u, w⟩
    simp only [hg, Prod.swap_prod_mk]
    by_cases hb : IsBoundary tri u w
    · have hb' : IsBoundary tri w u := (isBoundary_comm tri u w).mp hb
      simp [hb, hb']
    · have hb' : ¬ IsBoundary tri w u := fun h' => hb ((isBoundary_comm tri w u).mp h')
      have hsw := edgeVal_swap c (u, w)
      simp only [Prod.swap_prod_mk] at hsw
      simp [hb, hb', h u w hb, hsw]
  -- the non-boundary contribution vanishes
  have hzero : ∑ e ∈ E, (edgeCount tri e : ℤ) * g e = 0 := by
    have hX : ∑ e ∈ E, (edgeCount tri e : ℤ) * g e =
        ∑ e ∈ E, (edgeCount tri e.swap : ℤ) * g e.swap :=
      (Finset.sum_nbij' Prod.swap Prod.swap (fun e he => hswapE e he)
        (fun e he => hswapE e he) (fun e _ => Prod.swap_swap e) (fun e _ => Prod.swap_swap e)
        (fun e _ => by simp)).symm
    simp_rw [hanti, Finset.sum_neg_distrib] at hX
    linarith
  -- assemble
  have hsplit : index tri c + ∑ t, ((dirEdges (tri t)).map g).sum = content tri c := by
    unfold index content
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← sum_dirEdges_edgeVal]
    exact sum_map_filter_add _ _ _
  rw [sum_map_eq_sum_edgeCount tri g E hmemE, hzero, add_zero] at hsplit
  exact hsplit

/-- Sanity check: a single triangle coloured `0, 1, 2` has index and content `1`. -/
example : index (fun _ : Unit => ((0 : Fin 3), (1 : Fin 3), (2 : Fin 3))) id = 1 ∧
    content (fun _ : Unit => ((0 : Fin 3), (1 : Fin 3), (2 : Fin 3))) id = 1 := by
  decide

end Cslib.Simplicial
