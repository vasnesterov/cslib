/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Algorithms.Lean.StableMatching.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-! # The Gale–Shapley algorithm

A computable, deterministic version of the Gale–Shapley proposal algorithm [GaleShapley1962], with
the side `L` proposing, for sides of equal finite size. We run the "simultaneous" variant
(McVitie–Wilson style [McVitieWilson1971]): the state records, for each proposer `l`, the set of
receivers that have already rejected `l`; every proposer currently proposes to its best receiver
that has not rejected it, and in each round every proposer that is beaten at its current receiver
by a preferred proposer gets rejected.

## Main definitions

* `StableMatching.galeShapley`: the matching computed by the algorithm.

## Main results

* `StableMatching.galeShapley_isStable`: the output of Gale–Shapley is stable.
* `StableMatching.exists_stable`: a stable matching always exists.

## References

* [D. Gale, L. S. Shapley, *College Admissions and the Stability of Marriage*][GaleShapley1962]
* [D. G. McVitie, L. B. Wilson, *The Stable Marriage Problem*][McVitieWilson1971]
-/

@[expose] public section

namespace Cslib.StableMatching

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq R]

/-- The (unique) minimizer of an injective function `f` on a nonempty finset (computable). -/
def argminOn {α : Type*} (f : α → ℕ) (hf : Function.Injective f) (s : Finset α)
    (hs : s.Nonempty) : α :=
  s.choose (fun a => ∀ b ∈ s, f a ≤ f b) (by
    obtain ⟨a, ha, hmin⟩ := s.exists_min_image f hs
    exact ⟨a, ⟨ha, hmin⟩, fun b ⟨hb, hb'⟩ => hf (le_antisymm (hb' a ha) (hmin b hb))⟩)

theorem argminOn_mem {α : Type*} (f : α → ℕ) (hf : Function.Injective f) (s : Finset α)
    (hs : s.Nonempty) : argminOn f hf s hs ∈ s :=
  Finset.choose_mem _ _ _

theorem argminOn_le {α : Type*} (f : α → ℕ) (hf : Function.Injective f) (s : Finset α)
    (hs : s.Nonempty) : ∀ b ∈ s, f (argminOn f hf s hs) ≤ f b :=
  Finset.choose_property (fun a => ∀ b ∈ s, f a ≤ f b) s _

namespace GS

variable (p : Prefs L R) (h : Fintype.card L = Fintype.card R)

omit [DecidableEq R] in
theorem univ_nonempty_of_card (h : Fintype.card L = Fintype.card R) (l : L) :
    (Finset.univ : Finset R).Nonempty := by
  rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff, ← h]
  exact Fintype.card_pos_iff.2 ⟨l⟩

/-- State: `S l` is the set of receivers that have rejected `l`. The current proposal of `l` is
its favourite receiver not in `S l` (a junk value if there is none; this never happens). -/
def target (S : L → Finset R) (l : L) : R :=
  if hs : (S l)ᶜ.Nonempty then argminOn (p.rankL l) (p.injL l) _ hs
  else argminOn (p.rankL l) (p.injL l) Finset.univ (univ_nonempty_of_card h l)

/-- `m` is rejected in state `S`: some proposer that its current receiver prefers proposes to the
same receiver. -/
def Rejected (S : L → Finset R) (m : L) : Prop :=
  ∃ l', p.rankR (target p h S m) l' < p.rankR (target p h S m) m ∧
    target p h S l' = target p h S m

instance (S : L → Finset R) : DecidablePred (Rejected p h S) := fun _ => by
  unfold Rejected; infer_instance

/-- One round: every rejected proposer crosses its current receiver off its list. -/
def step (S : L → Finset R) : L → Finset R := fun m =>
  if Rejected p h S m then insert (target p h S m) (S m) else S m

theorem step_measure_lt (S : L → Finset R)
    (hc : ∃ m, Rejected p h S m ∧ target p h S m ∉ S m) :
    ∑ l, (step p h S l)ᶜ.card < ∑ l, (S l)ᶜ.card := by
  obtain ⟨m, hm, hnot⟩ := hc
  apply Finset.sum_lt_sum
  · intro l _
    unfold step
    split_ifs
    · exact Finset.card_le_card (Finset.compl_subset_compl.2 (Finset.subset_insert _ _))
    · exact le_rfl
  · refine ⟨m, Finset.mem_univ _, ?_⟩
    simp only [step, hm, ↓reduceIte]
    exact Finset.card_lt_card (Finset.compl_ssubset_compl.2 (Finset.ssubset_insert hnot))

/-- Iterate rounds until no proposer is rejected. -/
def loop (S : L → Finset R) : L → Finset R :=
  if _hc : ∃ m, Rejected p h S m ∧ target p h S m ∉ S m then loop (step p h S) else S
termination_by ∑ l, (S l)ᶜ.card
decreasing_by exact step_measure_lt p h S ‹_›

/-- Main invariant: every receiver that rejected `l` is currently proposed to by someone it
prefers to `l`. -/
def Inv (S : L → Finset R) : Prop :=
  ∀ l, ∀ r ∈ S l, ∃ l', p.rankR r l' < p.rankR r l ∧ target p h S l' = r

variable {p h}

theorem target_congr {S S' : L → Finset R} {l : L} (e : S' l = S l) :
    target p h S' l = target p h S l := by
  unfold target; simp only [e]

theorem Inv.compl_nonempty {S : L → Finset R} (hI : Inv p h S) (l : L) : (S l)ᶜ.Nonempty := by
  classical
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at hne
  have hsub : (Finset.univ : Finset R) ⊆ (Finset.univ.erase l).image (target p h S) := by
    intro r _
    obtain ⟨l', hlt, ht⟩ := hI l r (hne ▸ Finset.mem_univ r)
    refine Finset.mem_image.2 ⟨l', Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩, ht⟩
    rintro rfl
    exact lt_irrefl _ hlt
  have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Finset.card_univ, h] at hc
  have : 0 < Fintype.card R := h ▸ Fintype.card_pos_iff.2 ⟨l⟩
  omega

theorem Inv.target_not_mem {S : L → Finset R} (hI : Inv p h S) (l : L) :
    target p h S l ∉ S l := by
  have hs := hI.compl_nonempty l
  simp only [target, hs, ↓reduceDIte]
  exact Finset.mem_compl.1 (argminOn_mem _ _ _ hs)

/-- Proposers propose in order: everything better than the current proposal has rejected. -/
theorem Inv.mem_of_lt {S : L → Finset R} (hI : Inv p h S) (l : L) (r : R)
    (hr : p.rankL l r < p.rankL l (target p h S l)) : r ∈ S l := by
  have hs := hI.compl_nonempty l
  by_contra hrn
  simp only [target, hs, ↓reduceDIte] at hr
  exact absurd (argminOn_le _ _ _ hs r (Finset.mem_compl.2 hrn)) (not_le.2 hr)

theorem inv_empty : Inv p h (fun _ => ∅) := fun _ _ hr => absurd hr (Finset.notMem_empty _)

theorem Inv.step {S : L → Finset R} (hI : Inv p h S) : Inv p h (step p h S) := by
  intro l r hr
  have h0 : ∃ l₀, p.rankR r l₀ < p.rankR r l ∧ target p h S l₀ = r := by
    unfold GS.step at hr
    split_ifs at hr with hrej
    · rcases Finset.mem_insert.1 hr with rfl | hr
      · exact hrej
      · exact hI l r hr
    · exact hI l r hr
  obtain ⟨l₀, hlt₀, ht₀⟩ := h0
  obtain ⟨l₁, hl₁, hmin⟩ := (Finset.univ.filter (fun l' => target p h S l' = r)).exists_min_image
    (p.rankR r) ⟨l₀, by simp [ht₀]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl₁ hmin
  have hnrej : ¬ Rejected p h S l₁ := by
    rintro ⟨l', hlt, ht⟩
    rw [hl₁] at hlt ht
    exact absurd (hmin l' ht) (not_le.2 hlt)
  have hstep : GS.step p h S l₁ = S l₁ := by simp [GS.step, hnrej]
  exact ⟨l₁, (hmin l₀ ht₀).trans_lt hlt₀, (target_congr hstep).trans hl₁⟩

theorem loop_spec (S : L → Finset R) (hI : Inv p h S) :
    Inv p h (loop p h S) ∧ ∀ m, ¬ Rejected p h (loop p h S) m := by
  rw [loop]
  split_ifs with hc
  · exact loop_spec _ hI.step
  · push Not at hc
    exact ⟨hI, fun m hm => hI.target_not_mem m (hc m hm)⟩
termination_by ∑ l, (S l)ᶜ.card
decreasing_by exact step_measure_lt p h S hc

variable (p h) in
/-- The final state of the algorithm. -/
def finalState : L → Finset R := loop p h fun _ => ∅

theorem inv_finalState : Inv p h (finalState p h) := (loop_spec _ inv_empty).1

theorem not_rejected_finalState (m : L) : ¬ Rejected p h (finalState p h) m :=
  (loop_spec _ inv_empty).2 m

variable (p h) in
theorem target_finalState_injective : Function.Injective (target p h (finalState p h)) := by
  intro l₁ l₂ e
  rcases lt_trichotomy (p.rankR (target p h (finalState p h) l₁) l₁)
    (p.rankR (target p h (finalState p h) l₁) l₂) with hlt | heq | hgt
  · exact absurd ⟨l₁, e ▸ hlt, e⟩ (not_rejected_finalState l₂)
  · exact p.injR _ heq
  · exact absurd ⟨l₂, hgt, e.symm⟩ (not_rejected_finalState l₁)

variable (p h) in
theorem target_finalState_bijective : Function.Bijective (target p h (finalState p h)) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨target_finalState_injective p h, h⟩

end GS

/-- The Gale–Shapley matching (`L` proposes), as a computable deterministic algorithm. -/
def galeShapley (p : Prefs L R) (h : Fintype.card L = Fintype.card R) : L ≃ R where
  toFun := GS.target p h (GS.finalState p h)
  invFun := Fintype.bijInv (GS.target_finalState_bijective p h)
  left_inv := Fintype.leftInverse_bijInv _
  right_inv := Fintype.rightInverse_bijInv _

/-- The Gale–Shapley matching is stable [GaleShapley1962]. -/
theorem galeShapley_isStable (p : Prefs L R) (h : Fintype.card L = Fintype.card R) :
    p.IsStable (galeShapley p h) := by
  rintro l r ⟨h₁, h₂⟩
  have hI := GS.inv_finalState (p := p) (h := h)
  obtain ⟨l', hlt, ht⟩ := hI l r (hI.mem_of_lt l r h₁)
  have hsymm : (galeShapley p h).symm r = l' := (Equiv.symm_apply_eq _).2 ht.symm
  rw [hsymm] at h₂
  omega

omit [DecidableEq R] in
/-- A stable perfect matching always exists (sides of equal size, strict preferences). -/
theorem exists_stable (p : Prefs L R) (h : Fintype.card L = Fintype.card R) :
    ∃ μ : L ≃ R, p.IsStable μ := by
  classical
  exact ⟨galeShapley p h, galeShapley_isStable p h⟩

end Cslib.StableMatching
