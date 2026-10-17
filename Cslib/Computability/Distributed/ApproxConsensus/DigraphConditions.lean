/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Foundations.Combinatorics.Digraph.Walk
public import Cslib.Computability.Distributed.ApproxConsensus.Iterative
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Push

/-!
# Graph conditions for approximate Byzantine consensus on directed networks

Necessary and sufficient topological conditions for (iterative or asynchronous) approximate
Byzantine consensus on a digraph `G` with at most `f` faults, from Vaidya–Tseng–Liang
[VTL12, PODC 2012], Tseng–Vaidya [TV15, PODC 2015] and Sakavalas–Tseng–Vaidya [STV20, PODC 2020].
Reach sets are `Digraph.ReachableAvoiding`: `reach_v(X) = {w | G.ReachableAvoiding X w v}`.

## Main definitions

* `Reaches G X a b`: `b` is reachable from `a` avoiding the finite set `X`.
* `ReachCondIn G F k`: for every `u ∉ F ∪ Fu`, `v ∉ F ∪ Fv` with `|Fu|, |Fv| ≤ k`,
  `reach_v(F ∪ Fv) ∩ reach_u(F ∪ Fu) ≠ ∅`. The *1-, 2-, 3-reach* conditions of [STV20]
  (Definition 3) are `OneReach` (`k = 0`, all `|F| ≤ f`), `TwoReach` (`F = ∅`, `k = f`) and
  `ThreeReach` (all `|F| ≤ f`, `k = f`).
* `InArrow G x A B` (`A →ˣ B`): the set `B` has at least `x` in-neighbours in `A`.
  `PartCond G F k`: every partition `L, C, R` of `V \ F` with `L, R ≠ ∅` has
  `L ∪ C →^{k+1} R` or `R ∪ C →^{k+1} L`. Conditions CCS, CCA, BCS of [TV15].
* `Arrow G f A B` (`A ⇒ B` of [VTL12]): some *single* node of `B` has `f + 1` in-neighbours in
  `A`; `IterativeCondition G f`: the condition of [VTL12] for iterative algorithms.

## Main results

* `partCond_iff`: `PartCond G F k ↔ ReachCondIn G F k`; hence `ccs_iff_oneReach`,
  `cca_iff_twoReach`, `bcs_iff_threeReach` (Theorem 17 of [STV20]).
* `Arrow.inArrow`, `IterativeCondition.bcs`, `IterativeCondition.threeReach`: the iterative
  condition implies BCS (the converse does not hold in general).
-/

@[expose] public section

open Finset Digraph

namespace Cslib.ApproxConsensus

variable {V : Type*} [DecidableEq V] {G : Digraph V}

/-! ## Reach conditions -/

/-- `Reaches G X a b`: `a ∉ X` and `b` is reachable from `a` in the subgraph induced by `V \ X`
(`Digraph.ReachableAvoiding` for a `Finset` of removed nodes). The reach set of [STV20,
Definition 2] is `reach_v(X) = {u | Reaches G X u v}`. -/
abbrev Reaches (G : Digraph V) (X : Finset V) (a b : V) : Prop := G.ReachableAvoiding ↑X a b

omit [DecidableEq V] in
/-- `ReachableAvoiding.refl` with the forbidden set given as a `Finset`. -/
theorem Reaches.refl {X : Finset V} {a : V} (h : a ∉ X) : Reaches G X a a :=
  ReachableAvoiding.refl h

/-- The reach condition with "global" fault set `F` and local suspect sets of size `≤ k`:
for every `u ∉ F ∪ Fu`, `v ∉ F ∪ Fv` with `|Fu|, |Fv| ≤ k`,
`reach_v(F ∪ Fv) ∩ reach_u(F ∪ Fu) ≠ ∅`. -/
def ReachCondIn (G : Digraph V) (F : Finset V) (k : ℕ) : Prop :=
  ∀ (Fu Fv : Finset V) (u v : V), Fu.card ≤ k → Fv.card ≤ k → u ∉ F ∪ Fu → v ∉ F ∪ Fv →
    ∃ w, Reaches G (F ∪ Fv) w v ∧ Reaches G (F ∪ Fu) w u

/-- **1-reach** (Definition 3): for every `F` with `|F| ≤ f` and `u, v ∉ F`,
`reach_u(F) ∩ reach_v(F) ≠ ∅`. -/
def OneReach (G : Digraph V) (f : ℕ) : Prop :=
  ∀ (F : Finset V) (u v : V), F.card ≤ f → u ∉ F → v ∉ F →
    ∃ w, Reaches G F w v ∧ Reaches G F w u

/-- **2-reach** (Definition 3): for every `Fu, Fv` with `|Fu|, |Fv| ≤ f`, `u ∉ Fu`, `v ∉ Fv`,
`reach_v(Fv) ∩ reach_u(Fu) ≠ ∅`. -/
def TwoReach (G : Digraph V) (f : ℕ) : Prop :=
  ∀ (Fu Fv : Finset V) (u v : V), Fu.card ≤ f → Fv.card ≤ f → u ∉ Fu → v ∉ Fv →
    ∃ w, Reaches G Fv w v ∧ Reaches G Fu w u

/-- **3-reach** (Definition 3): for every `F, Fu, Fv` with `|F|, |Fu|, |Fv| ≤ f`, `u ∉ F ∪ Fu`,
`v ∉ F ∪ Fv`, `reach_v(F ∪ Fv) ∩ reach_u(F ∪ Fu) ≠ ∅`. -/
def ThreeReach (G : Digraph V) (f : ℕ) : Prop :=
  ∀ (F Fu Fv : Finset V) (u v : V), F.card ≤ f → Fu.card ≤ f → Fv.card ≤ f → u ∉ F ∪ Fu →
    v ∉ F ∪ Fv → ∃ w, Reaches G (F ∪ Fv) w v ∧ Reaches G (F ∪ Fu) w u

/-- 1-reach is the reach condition with `k = 0` for every `|F| ≤ f`. -/
theorem oneReach_iff {f : ℕ} : OneReach G f ↔ ∀ F : Finset V, F.card ≤ f → ReachCondIn G F 0 := by
  constructor
  · intro h F hF Fu Fv u v hu hv hu' hv'
    rw [Nat.le_zero, card_eq_zero] at hu hv
    subst hu hv
    simpa using h F u v hF (by simpa using hu') (by simpa using hv')
  · intro h F u v hF hu hv
    simpa using h F hF ∅ ∅ u v (by simp) (by simp) (by simpa using hu) (by simpa using hv)

/-- 2-reach is the reach condition with `F = ∅`, `k = f`. -/
theorem twoReach_iff {f : ℕ} : TwoReach G f ↔ ReachCondIn G ∅ f := by
  simp [TwoReach, ReachCondIn]

/-- 3-reach is the reach condition with `k = f` for every `|F| ≤ f`. -/
theorem threeReach_iff {f : ℕ} :
    ThreeReach G f ↔ ∀ F : Finset V, F.card ≤ f → ReachCondIn G F f := by
  constructor
  · intro h F hF Fu Fv u v hu hv hu' hv'; exact h F Fu Fv u v hF hu hv hu' hv'
  · intro h F Fu Fv u v hF hu hv hu' hv'; exact h F hF Fu Fv u v hu hv hu' hv'

/-! ## Small networks -/

section Card

variable [Fintype V]

/-- Every graph on at most one node satisfies 3-reach (both nodes of the condition coincide). -/
theorem threeReach_of_card_le_one {f : ℕ} (h : Fintype.card V ≤ 1) : ThreeReach G f := by
  intro F Fu Fv u v _ _ _ hu hv
  have huv : u = v := Fintype.card_le_one_iff.mp h u v
  subst huv
  exact ⟨u, Reaches.refl hv, Reaches.refl hu⟩

/-- In any graph with at least two nodes, 3-reach forces `n > 3f`. -/
theorem ThreeReach.three_mul_lt_card {f : ℕ} (hG : ThreeReach G f)
    (hn : 2 ≤ Fintype.card V) : 3 * f < Fintype.card V := by
  by_contra hcon
  push Not at hcon
  set n := Fintype.card V
  obtain ⟨u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < n)
  set W : Finset V := (univ.erase u).erase v
  have hW : W.card = n - 2 := by
    rw [card_erase_of_mem (by simp [huv.symm]), card_erase_of_mem (mem_univ _), card_univ]; omega
  have hf : 1 ≤ f := by omega
  obtain ⟨A, hAW, hA⟩ := exists_subset_card_eq (s := W) (n := min (f - 1) (n - 2)) (by omega)
  obtain ⟨B, hBW, hB⟩ := exists_subset_card_eq (s := W \ A) (n := min (f - 1) (n - 2 - A.card))
    (by rw [card_sdiff_of_subset hAW]; omega)
  set F := (W \ A) \ B
  have hFc : F.card ≤ f := by
    rw [card_sdiff_of_subset hBW, card_sdiff_of_subset hAW]; omega
  have hu : u ∉ F ∪ insert v A := by
    simp only [mem_union, mem_insert, F, W, mem_sdiff, mem_erase]
    refine fun h => ?_
    rcases h with h | h | h
    · exact h.1.1.2.1 rfl
    · exact huv h
    · have := hAW h; simp [W] at this
  have hv : v ∉ F ∪ insert u B := by
    simp only [mem_union, mem_insert, F, W, mem_sdiff, mem_erase]
    refine fun h => ?_
    rcases h with h | h | h
    · exact h.1.1.1 rfl
    · exact huv h.symm
    · have := (mem_sdiff.mp (hBW h)).1; simp [W] at this
  obtain ⟨w, hw1, hw2⟩ := hG F (insert v A) (insert u B) u v hFc
    (by rw [card_insert_of_notMem]; · omega
        intro h; have := hAW h; simp [W] at this) (by
      rw [card_insert_of_notMem]; · omega
      intro h; have := (mem_sdiff.mp (hBW h)).1; simp [W] at this) hu hv
  have h1 : w ∉ F ∪ insert u B := hw1.1
  have h2 : w ∉ F ∪ insert v A := hw2.1
  by_cases hwu : w = u
  · exact h1 (by simp [hwu])
  by_cases hwv : w = v
  · exact h2 (by simp [hwv])
  have hwW : w ∈ W := by simp [W, hwu, hwv]
  by_cases hwA : w ∈ A
  · exact h2 (by simp [hwA])
  by_cases hwB : w ∈ B
  · exact h1 (by simp [hwB])
  · exact h1 (mem_union_left _ (by simp [F, hwW, hwA, hwB]))

end Card

/-! ## Partition conditions -/

section Partition

variable [Fintype V]

/-- The in-neighbours of `B` inside `A`: the nodes of `A` with an arc into `B`. -/
noncomputable def inNbrsIn (G : Digraph V) (A B : Finset V) : Finset V := by
  classical exact A.filter fun a => ∃ b ∈ B, G.Adj a b

omit [DecidableEq V] [Fintype V] in
/-- Membership in `inNbrsIn G A B`. -/
@[simp] theorem mem_inNbrsIn {A B : Finset V} {a : V} :
    a ∈ inNbrsIn G A B ↔ a ∈ A ∧ ∃ b ∈ B, G.Adj a b := by
  classical simp [inNbrsIn]

/-- `A →ˣ B` (Definition 14 of [STV20]): the set `B` has at least `x` distinct incoming
neighbours in `A` (for disjoint `A`, `B`). -/
def InArrow (G : Digraph V) (x : ℕ) (A B : Finset V) : Prop := x ≤ #(inNbrsIn G A B)

/-- Partition condition on `V \ F`: for every partition `L, C, R` of `V \ F` with `L, R`
non-empty, `L ∪ C →^{k+1} R` or `R ∪ C →^{k+1} L`. -/
def PartCond (G : Digraph V) (F : Finset V) (k : ℕ) : Prop :=
  ∀ L C R : Finset V, Disjoint L C → Disjoint L R → Disjoint C R → L ∪ C ∪ R = univ \ F →
    L.Nonempty → R.Nonempty → InArrow G (k + 1) (L ∪ C) R ∨ InArrow G (k + 1) (R ∪ C) L

/-- Condition CCS of [TV15] (Definition 16 of [STV20]). -/
def CCS (G : Digraph V) (f : ℕ) : Prop := ∀ F : Finset V, F.card ≤ f → PartCond G F 0

/-- Condition CCA of [TV15] (Definition 17 of [STV20]). -/
def CCA (G : Digraph V) (f : ℕ) : Prop := PartCond G ∅ f

/-- Condition BCS of [TV15] (Definition 18 of [STV20]). -/
def BCS (G : Digraph V) (f : ℕ) : Prop := ∀ F : Finset V, F.card ≤ f → PartCond G F f

/-- The core equivalence behind Theorem 17: the partition condition on `V \ F` with threshold
`k + 1` is equivalent to the reach condition on `G − F` with suspect sets of size `≤ k`. -/
theorem partCond_iff {F : Finset V} {k : ℕ} : PartCond G F k ↔ ReachCondIn G F k := by
  classical
  constructor
  · intro h Fu Fv u v hFu hFv hu hv
    by_contra hcon
    push Not at hcon
    set L := univ.filter fun w => Reaches G (F ∪ Fv) w v
    set R := univ.filter fun w => Reaches G (F ∪ Fu) w u
    set C := ((univ \ F) \ L) \ R
    have hLF : ∀ w ∈ L, w ∉ F := fun w hw => by
      simp only [L, mem_filter] at hw; exact fun h => hw.2.1 (mem_union_left _ h)
    have hRF : ∀ w ∈ R, w ∉ F := fun w hw => by
      simp only [R, mem_filter] at hw; exact fun h => hw.2.1 (mem_union_left _ h)
    have hLR : Disjoint L R := disjoint_left.mpr fun w hwL hwR => by
      simp only [L, R, mem_filter, mem_univ, true_and] at hwL hwR
      exact hcon w hwL hwR
    have hU : L ∪ C ∪ R = univ \ F := by
      ext w; simp only [C, mem_union, mem_sdiff, mem_univ, true_and]
      constructor
      · rintro ((h | h) | h)
        · exact hLF w h
        · exact h.1.1
        · exact hRF w h
      · intro hw; tauto
    have hcl : ∀ (X W : Finset V) (z : V), (∀ w ∈ W, w ∉ F) → X.card ≤ k →
        (∀ a b, G.Adj a b → a ∉ F ∪ X → b ∈ W → a ∈ W) →
          ¬ (k + 1 ≤ (inNbrsIn G ((univ \ F) \ W) W).card) := by
      intro X W _ _ hX hcl hk
      have : inNbrsIn G ((univ \ F) \ W) W ⊆ X := by
        intro a ha
        simp only [inNbrsIn, mem_filter, mem_sdiff, mem_univ, true_and] at ha
        obtain ⟨⟨haF, haW⟩, b, hb, e⟩ := ha
        by_contra haX
        exact haW (hcl a b e (by simp [haF, haX]) hb)
      have := card_le_card this
      omega
    have eR : L ∪ C = (univ \ F) \ R := by
      rw [← hU]; ext w; simp only [mem_union, mem_sdiff]
      constructor
      · rintro (h | h)
        · exact ⟨Or.inl (Or.inl h), disjoint_left.mp hLR h⟩
        · exact ⟨Or.inl (Or.inr h), (mem_sdiff.mp h).2⟩
      · rintro ⟨(h | h) | h, h'⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h h'
    have eL : R ∪ C = (univ \ F) \ L := by
      rw [← hU]; ext w; simp only [mem_union, mem_sdiff, C]
      constructor
      · rintro (h | h)
        · exact ⟨Or.inr h, (disjoint_right.mp hLR h)⟩
        · exact ⟨Or.inl (Or.inr (by simp [h.1.1.1, h.1.1.2, h.1.2, h.2])), h.1.2⟩
      · rintro ⟨(h | h) | h, h'⟩
        · exact absurd h h'
        · exact Or.inr (by simpa [C] using h)
        · exact Or.inl h
    rcases h L C R (disjoint_left.mpr fun w hw hwC => (mem_sdiff.mp (mem_sdiff.mp hwC).1).2 hw)
        hLR (disjoint_left.mpr fun w hwC hw => (mem_sdiff.mp hwC).2 hw) hU
        ⟨v, by simp only [L, mem_filter, mem_univ, true_and]; exact .refl hv⟩
        ⟨u, by simp only [R, mem_filter, mem_univ, true_and]; exact .refl hu⟩ with h | h
    · rw [InArrow, eR] at h
      exact hcl Fu R u hRF hFu (fun a b e ha hb => by
        simp only [R, mem_filter, mem_univ, true_and] at hb ⊢
        exact hb.head e ha) h
    · rw [InArrow, eL] at h
      exact hcl Fv L v hLF hFv (fun a b e ha hb => by
        simp only [L, mem_filter, mem_univ, true_and] at hb ⊢
        exact hb.head e ha) h
  · intro h L C R hLC hLR hCR hU ⟨v, hv⟩ ⟨u, hu⟩
    by_contra hcon
    rw [not_or, InArrow, InArrow, not_le, not_le] at hcon
    set Fu := inNbrsIn G (L ∪ C) R
    set Fv := inNbrsIn G (R ∪ C) L
    have hmem : ∀ w, w ∉ F → w ∈ L ∨ w ∈ C ∨ w ∈ R := fun w hw => by
      have : w ∈ univ \ F := by simp [hw]
      rw [← hU] at this; simp only [mem_union] at this; tauto
    have hLF : ∀ w ∈ L, w ∉ F := fun w hw => by
      have : w ∈ univ \ F := hU ▸ mem_union_left _ (mem_union_left _ hw)
      exact (mem_sdiff.mp this).2
    have hRF : ∀ w ∈ R, w ∉ F := fun w hw => by
      have : w ∈ univ \ F := hU ▸ mem_union_right _ hw
      exact (mem_sdiff.mp this).2
    have hFvL : ∀ w ∈ Fv, w ∉ L := fun w hw => by
      simp only [Fv, inNbrsIn, mem_filter, mem_union] at hw
      rcases hw.1 with h | h
      · exact disjoint_right.mp hLR h
      · exact disjoint_right.mp hLC h
    have hFuR : ∀ w ∈ Fu, w ∉ R := fun w hw => by
      simp only [Fu, inNbrsIn, mem_filter, mem_union] at hw
      rcases hw.1 with h | h
      · exact disjoint_left.mp hLR h
      · exact disjoint_left.mp hCR h
    obtain ⟨w, hw1, hw2⟩ := h Fu Fv u v (by omega) (by omega)
      (by simp only [mem_union, not_or]; exact ⟨hRF u hu, fun h => hFuR u h hu⟩)
      (by simp only [mem_union, not_or]; exact ⟨hLF v hv, fun h => hFvL v h hv⟩)
    have hwL : w ∈ L := hw1.mem_of_closed (L := (L : Set V)) (fun a b e ha hb => by
      simp only [mem_coe, mem_union, not_or] at ha
      by_contra haL
      rcases hmem a ha.1 with h | h | h
      · exact haL h
      · exact ha.2 (by simp only [Fv, inNbrsIn, mem_filter, mem_union]; exact ⟨Or.inr h, b, hb, e⟩)
      · exact ha.2 (by simp only [Fv, inNbrsIn, mem_filter, mem_union]; exact ⟨Or.inl h, b, hb, e⟩))
      hv
    have hwR : w ∈ R := hw2.mem_of_closed (L := (R : Set V)) (fun a b e ha hb => by
      simp only [mem_coe, mem_union, not_or] at ha
      by_contra haR
      rcases hmem a ha.1 with h | h | h
      · exact ha.2 (by simp only [Fu, inNbrsIn, mem_filter, mem_union]; exact ⟨Or.inl h, b, hb, e⟩)
      · exact ha.2 (by simp only [Fu, inNbrsIn, mem_filter, mem_union]; exact ⟨Or.inr h, b, hb, e⟩)
      · exact haR h)
      hu
    exact disjoint_left.mp hLR hwL hwR

/-- CCS ⇔ 1-reach (Theorem 17 (a) of [STV20]). -/
theorem ccs_iff_oneReach {f : ℕ} : CCS G f ↔ OneReach G f := by
  rw [oneReach_iff]; exact forall₂_congr fun _ _ => partCond_iff

/-- CCA ⇔ 2-reach (Theorem 17 (b) of [STV20]). -/
theorem cca_iff_twoReach {f : ℕ} : CCA G f ↔ TwoReach G f := by
  rw [twoReach_iff]; exact partCond_iff

/-- BCS ⇔ 3-reach (Theorem 17 (c) of [STV20]). -/
theorem bcs_iff_threeReach {f : ℕ} : BCS G f ↔ ThreeReach G f := by
  rw [threeReach_iff]; exact forall₂_congr fun _ _ => partCond_iff

end Partition

/-! ## The iterative condition of [VTL12] -/

section Iterative

variable [Fintype V] {f : ℕ}

/-- `A ⇒ B` (Definition 1 of [VTL12]): some node `v ∈ B` has at least `f + 1` in-neighbours
in `A` (self-loops do not count). -/
def Arrow (G : Digraph V) (f : ℕ) (A B : Finset V) : Prop :=
  ∃ v ∈ B, f + 1 ≤ #(inNbrs G v ∩ A)

/-- The condition of Vaidya–Tseng–Liang for iterative approximate Byzantine consensus (statement
of Theorem 1 of [VTL12]): for every partition `F, L, C, R` of `V` with
`|F| ≤ f` and `L, R` non-empty, `C ∪ R ⇒ L` or `L ∪ C ⇒ R`. -/
def IterativeCondition (G : Digraph V) (f : ℕ) : Prop :=
  ∀ F L C R : Finset V, Disjoint F L → Disjoint F C → Disjoint F R → Disjoint L C →
    Disjoint L R → Disjoint C R → F ∪ L ∪ C ∪ R = univ → #F ≤ f → L.Nonempty → R.Nonempty →
    Arrow G f (C ∪ R) L ∨ Arrow G f (L ∪ C) R

/-- A set with at most `f` nodes cannot give `f + 1` in-neighbours: `¬ A ⇒ B`. -/
theorem not_arrow_of_card_le {A B : Finset V} (h : #A ≤ f) : ¬ Arrow G f A B := by
  rintro ⟨v, -, hv⟩
  have := card_le_card (inter_subset_right (s₁ := inNbrs G v) (s₂ := A))
  omega

/-- `A ⇒ B` is monotone in both sets. -/
theorem Arrow.mono {A A' B B' : Finset V} (h : Arrow G f A B) (hA : A ⊆ A') (hB : B ⊆ B') :
    Arrow G f A' B' := by
  obtain ⟨v, hv, hc⟩ := h
  exact ⟨v, hB hv, hc.trans (card_le_card (inter_subset_inter_left hA))⟩

/-- A decidable description of the in-neighbours (for `decide` on concrete digraphs). -/
theorem inNbrs_eq_filter [DecidableRel G.Adj] (v : V) :
    inNbrs G v = univ.filter fun j => G.Adj j v ∧ j ≠ v := by
  ext j; simp

/-- A single node with `f + 1` in-neighbours in `A` gives the set `B` `f + 1` in-neighbours. -/
theorem Arrow.inArrow {A B : Finset V} (h : Arrow G f A B) : InArrow G (f + 1) A B := by
  classical
  obtain ⟨v, hv, hc⟩ := h
  refine hc.trans (card_le_card fun a ha => ?_)
  simp only [mem_inter, mem_inNbrs] at ha
  exact mem_inNbrsIn.2 ⟨ha.2, v, hv, ha.1.1⟩

/-- The condition of Vaidya–Tseng–Liang (PODC 2012) for *iterative* approximate Byzantine
consensus implies BCS. -/
theorem IterativeCondition.bcs (h : IterativeCondition G f) : BCS G f := by
  classical
  intro F hF L C R hLC hLR hCR hU hL hR
  have hFL : Disjoint F L := disjoint_left.mpr fun x hx hxL => by
    have : x ∈ univ \ F := hU ▸ mem_union_left _ (mem_union_left _ hxL)
    exact (mem_sdiff.mp this).2 hx
  have hFC : Disjoint F C := disjoint_left.mpr fun x hx hxC => by
    have : x ∈ univ \ F := hU ▸ mem_union_left _ (mem_union_right _ hxC)
    exact (mem_sdiff.mp this).2 hx
  have hFR : Disjoint F R := disjoint_left.mpr fun x hx hxR => by
    have : x ∈ univ \ F := hU ▸ mem_union_right _ hxR
    exact (mem_sdiff.mp this).2 hx
  have hU' : F ∪ L ∪ C ∪ R = univ := by
    rw [union_assoc, union_assoc, ← union_assoc L, hU]; simp
  rcases h F L C R hFL hFC hFR hLC hLR hCR hU' hF hL hR with h | h
  · exact Or.inr (by rw [union_comm]; exact h.inArrow)
  · exact Or.inl h.inArrow

/-- The iterative condition of [VTL12] implies 3-reach: every graph on which iterative
approximate Byzantine consensus is possible also allows asynchronous approximate Byzantine
consensus. -/
theorem IterativeCondition.threeReach (h : IterativeCondition G f) : ThreeReach G f :=
  bcs_iff_threeReach.mp h.bcs

end Iterative

end Cslib.ApproxConsensus
