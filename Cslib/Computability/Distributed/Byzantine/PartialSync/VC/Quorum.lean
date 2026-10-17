/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.VC.Steps

/-!
# Vector consensus: quorum facts

Counting lemmas (`cnt`) and the consequences of prepare / commit quorums.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync.VC

open Finset

variable {P VI : Type*} [Fintype P] [DecidableEq P] {t : ℕ} {leader : ℕ → P}
  {F : Finset P} {inp : P → VI} (E : RoundRun (algo (VI := VI) t leader) F inp)

/-! ### Counting -/

set_option linter.unusedFintypeInType false in
omit [DecidableEq P] in
theorem cnt_mono {f g : P → Prop} (h : ∀ q, f q → g q) : cnt f ≤ cnt g :=
  Set.ncard_le_ncard (fun q hq => h q hq) (Set.toFinite _)

omit [DecidableEq P] in
theorem cnt_le_card (f : P → Prop) : cnt f ≤ Fintype.card P := by
  unfold cnt
  rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
  exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)

omit [DecidableEq P] in
/-- `cnt` as the cardinality of a filtered `Finset.univ`. -/
theorem cnt_eq_card_filter (f : P → Prop) [DecidablePred f] : cnt f = #(univ.filter f) := by
  rw [cnt, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

omit [DecidableEq P] in
/-- Two large sets intersect. -/
theorem exists_of_cnt_add {f g : P → Prop} (h : Fintype.card P < cnt f + cnt g) :
    ∃ q, f q ∧ g q := by
  classical
  rw [cnt_eq_card_filter, cnt_eq_card_filter] at h
  obtain ⟨q, hq⟩ := inter_nonempty_of_card_univ_lt_card_add_card h
  simp only [mem_inter, mem_filter, mem_univ, true_and] at hq
  exact ⟨q, hq⟩

omit [Fintype P] [DecidableEq P] in
theorem exists_of_cnt_pos {f : P → Prop} (h : 0 < cnt f) : ∃ q, f q :=
  Set.nonempty_of_ncard_ne_zero (Nat.pos_iff_ne_zero.mp h)

set_option linter.unusedFintypeInType false in
omit [DecidableEq P] in
/-- Removing the faulty processes. -/
theorem cnt_correct (f : P → Prop) : cnt f - F.card ≤ cnt (fun q => q ∉ F ∧ f q) := by
  unfold cnt
  beta_reduce
  have hs : {q | f q} ⊆ {q | q ∉ F ∧ f q} ∪ (F : Set P) := by
    intro q hq
    by_cases hqF : q ∈ F
    · exact Or.inr hqF
    · exact Or.inl ⟨hqF, hq⟩
  have := (Set.ncard_le_ncard hs (Set.toFinite _)).trans
    (Set.ncard_union_le _ _)
  rw [Set.ncard_coe_finset] at this
  omega

omit [DecidableEq P] in
theorem cnt_correct_all : cnt (fun q : P => q ∉ F) = Fintype.card P - F.card := by
  classical
  rw [cnt_eq_card_filter, ← card_compl]
  congr 1
  ext q
  simp

/-! ### Prepare quorums -/

/-- `PrepQ v m`: at least `n - t - |F|` correct processes accepted `m` in view `v`. -/
def PrepQ (v : ℕ) (m : Vec P VI) : Prop :=
  Fintype.card P - t - F.card ≤ cnt (fun q => q ∉ F ∧ (E.s (5 * v + 3) q).cur = some m)

/-- A prepared pair (of any process) is backed by a prepare quorum. -/
theorem prepQ_of_prepared {r : ℕ} {p : P} {v : ℕ} {m : Vec P VI}
    (h : (E.s r p).prepared = some (v, m)) : PrepQ E v m := by
  have h1 := (prepared_spec E h).2
  have h2 := cnt_correct (F := F) (fun q => E.rcv (5 * v + 3) p q = some (.prepare m))
  refine le_trans (by omega) (h2.trans (cnt_mono fun q hq => ⟨hq.1, rcv_3 E hq.1 hq.2⟩))

/-- At most one vector has a prepare quorum in a given view (`n > 3t`). -/
theorem prepQ_unique (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) {v : ℕ}
    {m m' : Vec P VI} (h : PrepQ E v m) (h' : PrepQ E v m') : m = m' := by
  unfold PrepQ at h h'
  by_contra hne
  -- both sets are disjoint subsets of the correct processes
  have hd : Disjoint {q | q ∉ F ∧ (E.s (5 * v + 3) q).cur = some m}
      {q | q ∉ F ∧ (E.s (5 * v + 3) q).cur = some m'} := by
    rw [Set.disjoint_left]; intro q h1 h2
    exact hne (Option.some.inj (h1.2.symm.trans h2.2))
  have hsub : {q | q ∉ F ∧ (E.s (5 * v + 3) q).cur = some m} ∪
      {q | q ∉ F ∧ (E.s (5 * v + 3) q).cur = some m'} ⊆ {q | q ∉ F} := by
    intro q hq; rcases hq with hq | hq <;> exact hq.1
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)] at h1
  have h2 := cnt_correct_all (F := F)
  unfold cnt at h h' h2
  beta_reduce at h h' h2
  omega

/-- A decision is backed by a commit quorum: at least `n - t - |F|` correct processes prepared
`(u, m)` in view `u` (at round `5u + 4`). -/
theorem commit_quorum_of_dec {r : ℕ} {p : P} {m : Vec P VI} (h : (E.s r p).dec = some m) :
    ∃ u, 5 * u + 5 ≤ r ∧ Fintype.card P - t - F.card ≤
      cnt (fun q => q ∉ F ∧ (E.s (5 * u + 4) q).prepared = some (u, m)) := by
  obtain ⟨u, hu, hq⟩ := dec_spec E h
  refine ⟨u, hu, ?_⟩
  have h2 := cnt_correct (F := F) (fun q => E.rcv (5 * u + 4) p q = some (.commit m))
  exact le_trans (by omega) (h2.trans (cnt_mono fun q hq => ⟨hq.1, rcv_4 E hq.1 hq.2⟩))

end Cslib.Byzantine.PartialSync.VC
