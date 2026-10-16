/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Arboricity and low out-degree orientations

## Main definitions

* `SimpleGraph.ArboricityLE G α`: the edges of `G` can be covered by `α` forests (equivalently,
  partitioned: subgraphs of forests are forests). The arboricity of `G` is the least such `α`.
* `SimpleGraph.OutOrientation G α`: an orientation of the edges of `G` in which every vertex has
  out-degree at most `α`, given by out-neighbour sets `out v`. Every edge is oriented at least one
  way (orienting an edge both ways is allowed; it only makes the out-degree bound harder).
* `SimpleGraph.HasOutDegLE G α`: such an orientation exists.

## Main results

* `SimpleGraph.ArboricityLE.hasOutDegLE`: arboricity `≤ α` gives an orientation with out-degree
  `≤ α` (root every tree of every forest and orient edges towards the root).
* `SimpleGraph.isAcyclic_of_rank`: a graph with a rank function `f` such that adjacent vertices have
  different ranks and every vertex has at most one neighbour of smaller rank is acyclic.
* `SimpleGraph.OutOrientation.arboricityLE_of_rank`: an *acyclic* orientation (out-edges strictly
  decrease a rank function) with out-degree `≤ α` gives arboricity `≤ α`.

## References

* M. Dory, M. Ghaffari, S. Ilchi, *Near-Optimal Distributed Dominating Set in Bounded Arboricity
  Graphs*, PODC 2022 (Observation 3.5).
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The edges of `G` can be covered by `α` forests. -/
def ArboricityLE (α : ℕ) : Prop :=
  ∃ F : Fin α → SimpleGraph V, (∀ i, F i ≤ G) ∧ (∀ i, (F i).IsAcyclic) ∧
    ∀ ⦃u v⦄, G.Adj u v → ∃ i, (F i).Adj u v

/-- An orientation of `G` with out-degree at most `α`: `v ∈ out u` means that the edge `uv` is
oriented from `u` to `v`. -/
structure OutOrientation (α : ℕ) where
  /-- The out-neighbours of a vertex. -/
  out : V → Finset V
  adj_of_mem : ∀ ⦃u v⦄, v ∈ out u → G.Adj u v
  mem_or_mem : ∀ ⦃u v⦄, G.Adj u v → v ∈ out u ∨ u ∈ out v
  card_out_le : ∀ v, (out v).card ≤ α

/-- `G` has an orientation with out-degree at most `α`. -/
def HasOutDegLE (α : ℕ) : Prop := Nonempty (G.OutOrientation α)

variable {G}

/-- In a forest, two paths from `u` to the same endpoint coincide (up to `Walk.copy`). -/
private lemma IsAcyclic.eq_copy_of_isPath {F : SimpleGraph V} (hF : F.IsAcyclic) {u w w' : V}
    {p : F.Walk u w} {q : F.Walk u w'} (hp : p.IsPath) (hq : q.IsPath) (h : w' = w) :
    p = q.copy rfl h := by
  subst h
  simpa using congrArg Subtype.val ((hF.subsingleton_path _ _).elim ⟨p, hp⟩ ⟨q, hq⟩)

/-- A forest has an orientation with out-degree at most `1` (orient every edge towards a fixed
root of its tree). -/
lemma IsAcyclic.exists_outDegLE_one {F : SimpleGraph V} (hF : F.IsAcyclic) :
    ∃ o : V → Set V, (∀ v, (o v).Subsingleton) ∧ (∀ ⦃u v⦄, v ∈ o u → F.Adj u v) ∧
      ∀ ⦃u v⦄, F.Adj u v → v ∈ o u ∨ u ∈ o v := by
  classical
  let rt : V → V := fun v => Quot.out (F.connectedComponentMk v)
  have hrt : ∀ v, F.Reachable v (rt v) := fun v =>
    ConnectedComponent.eq.mp (Quot.out_eq (F.connectedComponentMk v)).symm
  let P : ∀ v, F.Walk v (rt v) := fun v => (hrt v).some.bypass
  have hP : ∀ v, (P v).IsPath := fun v => Walk.bypass_isPath _
  refine ⟨fun v => if (P v).Nil then ∅ else {(P v).snd}, fun v => ?_, fun u v h => ?_,
    fun u v huv => ?_⟩
  · dsimp only; split_ifs <;> simp
  · dsimp only at h; split_ifs at h with hn
    · simp at h
    · rw [Set.mem_singleton_iff] at h; subst h; exact Walk.adj_snd hn
  · have hr : rt v = rt u := by
      simp only [rt]; rw [ConnectedComponent.eq.mpr huv.reachable]
    by_cases hu : u ∈ (P v).support
    · right
      have hT := (hP v).takeUntil hu
      have hT' : (P v).takeUntil u hu = Walk.cons huv.symm Walk.nil := by
        simpa using hF.eq_copy_of_isPath hT (q := Walk.cons huv.symm Walk.nil)
          (by simp [huv.ne.symm]) rfl
      have hPv : P v = Walk.cons huv.symm ((P v).dropUntil u hu) := by
        conv_lhs => rw [← (P v).take_spec hu, hT']
        rfl
      dsimp only
      rw [hPv]
      simp
    · left
      have hPu := hF.eq_copy_of_isPath (hP u) (Walk.IsPath.cons (h := huv) (hP v) hu) hr
      dsimp only
      rw [hPu]
      simp [Walk.snd]

/-- Observation 3.5 of Dory–Ghaffari–Ilchi (PODC'22): a graph of arboricity at most `α` has an
orientation with out-degree at most `α`. -/
theorem ArboricityLE.hasOutDegLE {α : ℕ} (h : G.ArboricityLE α) :
    G.HasOutDegLE α := by
  classical
  obtain ⟨F, hFG, hF, hcov⟩ := h
  choose o ho1 ho2 ho3 using fun i => (hF i).exists_outDegLE_one
  refine ⟨{ out := fun v => Finset.univ.biUnion fun i => (ho1 i v).finite.toFinset
            adj_of_mem := fun u v h => ?_
            mem_or_mem := fun u v h => ?_
            card_out_le := fun v => ?_ }⟩
  · simp only [Finset.mem_biUnion, Finset.mem_univ, Set.Finite.mem_toFinset, true_and] at h
    obtain ⟨i, hi⟩ := h
    exact hFG i (ho2 i hi)
  · obtain ⟨i, hi⟩ := hcov h
    simp only [Finset.mem_biUnion, Finset.mem_univ, Set.Finite.mem_toFinset, true_and]
    exact (ho3 i hi).imp (fun h => ⟨i, h⟩) (fun h => ⟨i, h⟩)
  · refine Finset.card_biUnion_le.trans ?_
    calc ∑ i, ((ho1 i v).finite.toFinset).card ≤ ∑ _i : Fin α, 1 :=
          Finset.sum_le_sum fun i _ => Finset.card_le_one.mpr fun a ha b hb =>
            ho1 i v (by simpa using ha) (by simpa using hb)
      _ = α := by simp

/-- A graph with a rank function such that adjacent vertices have different ranks and every vertex
has at most one neighbour of smaller rank is a forest. -/
theorem isAcyclic_of_rank (f : V → ℕ) (hne : ∀ ⦃u v⦄, G.Adj u v → f u ≠ f v)
    (huniq : ∀ ⦃v u u'⦄, G.Adj v u → G.Adj v u' → f u < f v → f u' < f v → u = u') :
    G.IsAcyclic := by
  classical
  intro x c hc
  obtain ⟨z, hz, hmax⟩ := c.support.toFinset.exists_max_image f ⟨x, by simp⟩
  rw [List.mem_toFinset] at hz
  have hc' := hc.rotate hz
  have hnil := hc'.not_nil
  have hmem : ∀ w ∈ (c.rotate z hz).support, f w ≤ f z := fun w hw =>
    hmax w (List.mem_toFinset.2 ((c.mem_support_rotate_iff z hz).1 hw))
  have ha : G.Adj z (c.rotate z hz).snd := Walk.adj_snd hnil
  have hb : G.Adj z (c.rotate z hz).penultimate := (Walk.adj_penultimate hnil).symm
  exact hc'.snd_ne_penultimate <| huniq ha hb
    (lt_of_le_of_ne (hmem _ (Walk.getVert_mem_support _ _)) (hne ha).symm)
    (lt_of_le_of_ne (hmem _ (Walk.getVert_mem_support _ _)) (hne hb).symm)

/-- An orientation with out-degree `≤ α` along which a rank function strictly decreases (an acyclic
orientation) shows that `G` has arboricity at most `α`. -/
theorem OutOrientation.arboricityLE_of_rank {α : ℕ} (o : G.OutOrientation α)
    (f : V → ℕ) (hf : ∀ ⦃u v⦄, v ∈ o.out u → f v < f u) : G.ArboricityLE α := by
  -- label the out-edges of each vertex injectively by `Fin α`
  let lab : ∀ u, {v // v ∈ o.out u} → Fin α := fun u w =>
    Fin.castLE (o.card_out_le u) ((o.out u).equivFin w)
  have hlab : ∀ u, Function.Injective (lab u) := fun u =>
    (Fin.castLE_injective _).comp (o.out u).equivFin.injective
  let R : Fin α → V → V → Prop := fun i u v => ∃ h : v ∈ o.out u, lab u ⟨v, h⟩ = i
  refine ⟨fun i => SimpleGraph.fromRel (R i), fun i u v h => ?_, fun i => ?_, fun u v h => ?_⟩
  · obtain ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩ := h
    exacts [o.adj_of_mem h, (o.adj_of_mem h).symm]
  · -- a lower-rank neighbour in forest `i` is an out-neighbour with label `i`
    have key : ∀ ⦃v u⦄, (fromRel (R i)).Adj v u → f u < f v → R i v u := by
      rintro v u ⟨-, h | ⟨h, -⟩⟩ hlt
      · exact h
      · exact absurd (hf h) hlt.not_gt
    refine isAcyclic_of_rank f (fun u v h => ?_) (fun v u u' h h' hu hu' => ?_)
    · obtain ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩ := h
      exacts [(hf h).ne', (hf h).ne]
    · obtain ⟨hm, hl⟩ := key h hu
      obtain ⟨hm', hl'⟩ := key h' hu'
      exact congrArg Subtype.val (hlab v (hl.trans hl'.symm))
  · rcases o.mem_or_mem h with hm | hm
    · exact ⟨lab u ⟨v, hm⟩, h.ne, Or.inl ⟨hm, rfl⟩⟩
    · exact ⟨lab v ⟨u, hm⟩, h.ne, Or.inr ⟨hm, rfl⟩⟩

end SimpleGraph
