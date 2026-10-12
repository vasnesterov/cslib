/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The greedy maximal independent set for a given order

Given a graph `G` on `V`, a set `A` of *present* vertices and a rank function `r : V → ℕ` (the
order in
which the sequential greedy algorithm scans the vertices; for random greedy `r` comes from a
uniformly
random permutation), the greedy MIS `G.greedyMIS A r` is the unique set `M` with

  `v ∈ M ↔ v ∈ A ∧ ∀ w, G.Adj w v → r w < r v → w ∉ M`

("a vertex joins iff none of its earlier neighbours joined"). Vertices outside `A` are treated as
absent:
they never join and never block anybody. This lets one compare graphs differing by a vertex on a
fixed
vertex type.

We also define the **partial greedy evaluation** `G.partialGreedy A r x : V → Option Bool`, the
greedy
MIS computed in Kleene's three-valued logic when the state of one vertex `x` is unknown (`none`):
a vertex is out as soon as one earlier neighbour is surely in, in as soon as all earlier neighbours
are
surely out, and unknown otherwise. Its `none`-set `G.influenced A r x` is the set of vertices whose
greedy state may depend on the state of `x` — the set of "influenced nodes" in the dynamic MIS
analysis
of Censor-Hillel, Haramaty and Karnin (PODC 2016).

## Main definitions

* `SimpleGraph.greedyMIS G A r` — the greedy MIS of `G[A]` for the order given by `r`.
* `SimpleGraph.IsGreedyExcept G A r x s` — `s` satisfies the greedy rule at every vertex except `x`.
* `SimpleGraph.partialGreedy G A r x` — three-valued greedy evaluation with `x` unknown.
* `SimpleGraph.influenced G A r x` — the vertices left undetermined.

## Main results

* `greedyMIS_iff` (unfolding), `isGreedyExcept_greedyMIS`, `eq_greedyMIS_of_isGreedy` (uniqueness).
* `greedyMIS_independent`, `greedyMIS_maximal`: for injective `r` it is a maximal independent set
  of `G[A]`.
* `partialGreedy_eq_some_iff`: determined values agree with *every* state vector that is greedy
  except
  at `x`; `mem_influenced_of_ne`: in particular two such vectors can only differ on `influenced`.
* `influenced_eq_of_moveFirst`, `exists_influenced_lt_of_not_mem`: comparing `r` with the order in
  which
  `x` is moved to the front.
* `partialGreedy_eq_of_reorder`: the influenced set (for `x` first) is invariant under reorderings
  that preserve the relative order inside and outside of it.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (A : Set V) (r : V → ℕ)

/-- The greedy MIS of `G` restricted to the present vertices `A`, scanning vertices by increasing
rank `r`: a present vertex joins iff no earlier neighbour joined. -/
noncomputable def greedyMIS : Set V :=
  (InvImage.wf r wellFounded_lt).fix fun v ih =>
    v ∈ A ∧ ∀ w (h : r w < r v), G.Adj w v → ¬ ih w h

theorem greedyMIS_iff {v : V} :
    v ∈ G.greedyMIS A r ↔ v ∈ A ∧ ∀ w, G.Adj w v → r w < r v → w ∉ G.greedyMIS A r := by
  change (InvImage.wf r wellFounded_lt).fix (C := fun _ => Prop) _ v ↔ _
  rw [WellFounded.fix_eq]
  exact and_congr_right fun _ => ⟨fun h w hw hr => h w hr hw, fun h w hr hw => h w hw hr⟩

/-- Induction along the rank function. -/
theorem rank_induction {P : V → Prop} (h : ∀ v, (∀ w, r w < r v → P w) → P v) (v : V) : P v :=
  (InvImage.wf r wellFounded_lt).induction v h

/-- Any set satisfying the greedy rule at every vertex is the greedy MIS. -/
theorem eq_greedyMIS_of_isGreedy {s : Set V}
    (h : ∀ v, v ∈ s ↔ v ∈ A ∧ ∀ w, G.Adj w v → r w < r v → w ∉ s) : s = G.greedyMIS A r := by
  ext v
  induction v using rank_induction r with
  | h v ih =>
    rw [h, greedyMIS_iff]
    refine and_congr_right fun _ => forall_congr' fun w => forall_congr' fun _ =>
      forall_congr' fun hw => not_congr (ih w hw)

theorem greedyMIS_subset : G.greedyMIS A r ⊆ A := fun _ hv => ((G.greedyMIS_iff A r).1 hv).1

/-- For an injective rank function the greedy MIS is independent. -/
theorem greedyMIS_independent (hr : Function.Injective r) {u v : V} (hu : u ∈ G.greedyMIS A r)
    (hv : v ∈ G.greedyMIS A r) : ¬ G.Adj u v := by
  intro huv
  rcases lt_or_gt_of_ne (hr.ne huv.ne) with h | h
  · exact ((G.greedyMIS_iff A r).1 hv).2 u huv h hu
  · exact ((G.greedyMIS_iff A r).1 hu).2 v huv.symm h hv

/-- The greedy MIS is maximal among the present vertices. -/
theorem greedyMIS_maximal {v : V} (hvA : v ∈ A) (hv : v ∉ G.greedyMIS A r) :
    ∃ w ∈ G.greedyMIS A r, G.Adj w v ∧ r w < r v := by
  by_contra! h
  exact hv ((G.greedyMIS_iff A r).2 ⟨hvA, fun w hw hr hm => (h w hm hw).not_gt hr⟩)

/-- The greedy MIS only depends on the relative order of adjacent present vertices. -/
theorem greedyMIS_congr_rank {r' : V → ℕ}
    (h : ∀ u v, u ∈ A → v ∈ A → G.Adj u v → (r u < r v ↔ r' u < r' v)) :
    G.greedyMIS A r = G.greedyMIS A r' := by
  refine G.eq_greedyMIS_of_isGreedy A r' fun v => ?_
  rw [greedyMIS_iff]
  refine and_congr_right fun hvA => forall_congr' fun w => forall_congr' fun hw => ?_
  by_cases hwA : w ∈ A
  · rw [h w v hwA hvA hw]
  · have : w ∉ G.greedyMIS A r := fun hm => hwA (G.greedyMIS_subset A r hm)
    simp [this]

/-- `s` satisfies the greedy rule at every vertex other than `x` (the state of `x` is arbitrary). -/
def IsGreedyExcept (x : V) (s : Set V) : Prop :=
  ∀ v, v ≠ x → (v ∈ s ↔ v ∈ A ∧ ∀ w, G.Adj w v → r w < r v → w ∉ s)

theorem isGreedyExcept_greedyMIS (x : V) : G.IsGreedyExcept A r x (G.greedyMIS A r) :=
  fun _ _ => G.greedyMIS_iff A r

/-- Changing the presence of `x` only: the greedy MIS for `A'` is greedy except at `x` for `A`. -/
theorem isGreedyExcept_greedyMIS_of_eqOn {A' : Set V} {x : V} (hA : ∀ v, v ≠ x → (v ∈ A' ↔ v ∈ A)) :
    G.IsGreedyExcept A r x (G.greedyMIS A' r) := fun v hv => by
  rw [greedyMIS_iff, hA v hv]

/-! ### Three-valued greedy evaluation with one unknown vertex -/

open Classical in
/-- Greedy MIS evaluated in Kleene's three-valued logic when the state of `x` is unknown:
`some true` = surely in, `some false` = surely out, `none` = undetermined. -/
noncomputable def partialGreedy (x : V) : V → Option Bool :=
  (InvImage.wf r wellFounded_lt).fix fun v ih =>
    if v = x then none
    else if v ∉ A then some false
    else if ∃ w, ∃ h : r w < r v, G.Adj w v ∧ ih w h = some true then some false
    else if ∀ w, ∀ h : r w < r v, G.Adj w v → ih w h = some false then some true
    else none

open Classical in
theorem partialGreedy_eq (x v : V) : G.partialGreedy A r x v =
    if v = x then none
    else if v ∉ A then some false
    else if ∃ w, r w < r v ∧ G.Adj w v ∧ G.partialGreedy A r x w = some true then some false
    else if ∀ w, r w < r v → G.Adj w v → G.partialGreedy A r x w = some false then some true
    else none := by
  rw [partialGreedy, WellFounded.fix_eq]
  simp only [exists_prop]

/-- The vertices whose greedy state is not determined without knowing the state of `x`. -/
def influenced (x : V) : Set V := {v | G.partialGreedy A r x v = none}

variable {G A r}

@[simp] theorem partialGreedy_self (x : V) : G.partialGreedy A r x x = none := by
  rw [partialGreedy_eq]; simp

theorem self_mem_influenced (x : V) : x ∈ G.influenced A r x := partialGreedy_self x

/-- Case analysis on the unfolding of `partialGreedy` at a vertex `v ≠ x` of `A`. -/
private theorem partialGreedy_cases {x v : V} (h1 : v ≠ x) (h2 : v ∈ A) :
    ((∃ w, r w < r v ∧ G.Adj w v ∧ G.partialGreedy A r x w = some true) ∧
        G.partialGreedy A r x v = some false) ∨
    ((¬ ∃ w, r w < r v ∧ G.Adj w v ∧ G.partialGreedy A r x w = some true) ∧
      (∀ w, r w < r v → G.Adj w v → G.partialGreedy A r x w = some false) ∧
        G.partialGreedy A r x v = some true) ∨
    ((¬ ∃ w, r w < r v ∧ G.Adj w v ∧ G.partialGreedy A r x w = some true) ∧
      (¬ ∀ w, r w < r v → G.Adj w v → G.partialGreedy A r x w = some false) ∧
        G.partialGreedy A r x v = none) := by
  rw [partialGreedy_eq]
  simp only [h1, h2, not_true_eq_false, ↓reduceIte]
  split_ifs with h3 h4
  · exact Or.inl ⟨h3, rfl⟩
  · exact Or.inr (Or.inl ⟨h3, h4, rfl⟩)
  · exact Or.inr (Or.inr ⟨h3, h4, rfl⟩)

theorem partialGreedy_of_notMem {x v : V} (hv : v ∉ A) (h1 : v ≠ x) :
    G.partialGreedy A r x v = some false := by
  rw [partialGreedy_eq]; simp [h1, hv]

theorem partialGreedy_eq_some_true_iff {x v : V} :
    G.partialGreedy A r x v = some true ↔
      v ≠ x ∧ v ∈ A ∧ ∀ w, G.Adj w v → r w < r v → G.partialGreedy A r x w = some false := by
  by_cases h1 : v = x
  · subst h1; simp
  by_cases h2 : v ∈ A
  swap
  · simp [partialGreedy_of_notMem h2 h1, h2]
  rcases partialGreedy_cases (G := G) (r := r) h1 h2 with
    ⟨⟨w, hw, hwv, hwt⟩, h⟩ | ⟨-, h4, h⟩ | ⟨-, h4, h⟩
  · simp only [h, Option.some.injEq, Bool.false_eq_true, false_iff, not_and]
    exact fun _ _ h => by simp [h w hwv hw] at hwt
  · simp only [h, true_iff]
    exact ⟨h1, h2, fun w hwv hw => h4 w hw hwv⟩
  · simp only [h, reduceCtorEq, false_iff, not_and]
    exact fun _ _ h => h4 fun w hw hwv => h w hwv hw

theorem partialGreedy_eq_some_false_iff {x v : V} :
    G.partialGreedy A r x v = some false ↔
      v ≠ x ∧ (v ∉ A ∨ ∃ w, G.Adj w v ∧ r w < r v ∧ G.partialGreedy A r x w = some true) := by
  by_cases h1 : v = x
  · subst h1; simp
  by_cases h2 : v ∈ A
  swap
  · simp [partialGreedy_of_notMem h2 h1, h2, h1]
  rcases partialGreedy_cases (G := G) (r := r) h1 h2 with
    ⟨⟨w, hw, hwv, hwt⟩, h⟩ | ⟨h3, h4, h⟩ | ⟨h3, h4, h⟩
  · simp only [h, true_iff]
    exact ⟨h1, Or.inr ⟨w, hwv, hw, hwt⟩⟩
  · simp only [h, Option.some.injEq, Bool.true_eq_false, false_iff, not_and]
    rintro - (h | ⟨w, hwv, hw, hwt⟩)
    · exact h h2
    · exact h3 ⟨w, hw, hwv, hwt⟩
  · simp only [h, reduceCtorEq, false_iff, not_and]
    rintro - (h | ⟨w, hwv, hw, hwt⟩)
    · exact h h2
    · exact h3 ⟨w, hw, hwv, hwt⟩

theorem partialGreedy_eq_none_iff {x v : V} :
    G.partialGreedy A r x v = none ↔ v = x ∨ (v ∈ A ∧
      (∀ w, G.Adj w v → r w < r v → G.partialGreedy A r x w ≠ some true) ∧
      ∃ w, G.Adj w v ∧ r w < r v ∧ G.partialGreedy A r x w = none) := by
  by_cases h1 : v = x
  · subst h1; simp
  by_cases h2 : v ∈ A
  swap
  · simp [partialGreedy_of_notMem h2 h1, h2, h1]
  rcases partialGreedy_cases (G := G) (r := r) h1 h2 with
    ⟨⟨w, hw, hwv, hwt⟩, h⟩ | ⟨h3, h4, h⟩ | ⟨h3, h4, h⟩
  · simp only [h, reduceCtorEq, false_iff, h1, false_or, not_and]
    exact fun _ h => absurd hwt (h w hwv hw)
  · simp only [h, reduceCtorEq, false_iff, h1, false_or, not_and, not_exists]
    exact fun _ _ w hwv hw => by simp [h4 w hw hwv]
  · simp only [h, true_iff]
    refine Or.inr ⟨h2, fun w hwv hw hwt => h3 ⟨w, hw, hwv, hwt⟩, ?_⟩
    push Not at h4
    obtain ⟨w, hw, hwv, hwf⟩ := h4
    refine ⟨w, hwv, hw, ?_⟩
    rcases hval : G.partialGreedy A r x w with _ | _ | _
    · rfl
    · exact absurd hval hwf
    · exact absurd ⟨w, hw, hwv, hval⟩ h3

/-! ### Determined values -/

/-- Determined values of the partial evaluation agree with every state vector that satisfies the
greedy rule except at `x`. -/
theorem mem_iff_of_partialGreedy_eq_some {x : V} {s : Set V} (hs : G.IsGreedyExcept A r x s) :
    ∀ v b, G.partialGreedy A r x v = some b → (v ∈ s ↔ b = true) := by
  intro v
  induction v using rank_induction r with
  | h v ih =>
  intro b hb
  cases b with
  | true =>
    obtain ⟨hvx, hvA, hpred⟩ := partialGreedy_eq_some_true_iff.1 hb
    simp only [iff_true]
    exact (hs v hvx).2 ⟨hvA, fun w hwv hw hws => by
      simpa using (ih w hw false (hpred w hwv hw)).1 hws⟩
  | false =>
    obtain ⟨hvx, h⟩ := partialGreedy_eq_some_false_iff.1 hb
    simp only [Bool.false_eq_true, iff_false]
    intro hvs
    obtain ⟨hvA, hpred⟩ := (hs v hvx).1 hvs
    rcases h with h | ⟨w, hwv, hw, hwt⟩
    · exact h hvA
    · exact hpred w hwv hw ((ih w hw true hwt).2 rfl)

/-- Two state vectors that are greedy except at `x` can only differ on `influenced`. -/
theorem mem_influenced_of_mem_of_notMem {x v : V} {s₁ s₂ : Set V}
    (hs₁ : G.IsGreedyExcept A r x s₁) (hs₂ : G.IsGreedyExcept A r x s₂) (h₁ : v ∈ s₁)
    (h₂ : v ∉ s₂) : v ∈ G.influenced A r x := by
  rcases hv : G.partialGreedy A r x v with _ | b
  · exact hv
  · exact absurd ((mem_iff_of_partialGreedy_eq_some hs₂ v b hv).2
      ((mem_iff_of_partialGreedy_eq_some hs₁ v b hv).1 h₁)) h₂

/-- Vertices before `x` are determined. -/
theorem notMem_influenced_of_lt {x v : V} (h : r v < r x) : v ∉ G.influenced A r x := by
  induction v using rank_induction r with
  | h v ih =>
  intro hv
  rcases partialGreedy_eq_none_iff.1 hv with rfl | ⟨-, -, w, -, hw, hwn⟩
  · exact lt_irrefl _ h
  · exact ih w hw (hw.trans h) hwn

/-- Before `x`, all state vectors that are greedy except at `x` agree. -/
theorem mem_iff_mem_of_lt {x v : V} {s₁ s₂ : Set V} (hs₁ : G.IsGreedyExcept A r x s₁)
    (hs₂ : G.IsGreedyExcept A r x s₂) (h : r v < r x) : v ∈ s₁ ↔ v ∈ s₂ :=
  ⟨fun h₁ => by_contra fun h₂ => notMem_influenced_of_lt h
      (mem_influenced_of_mem_of_notMem hs₁ hs₂ h₁ h₂),
    fun h₂ => by_contra fun h₁ => notMem_influenced_of_lt h
      (mem_influenced_of_mem_of_notMem hs₂ hs₁ h₂ h₁)⟩

/-- If `s` is greedy except at `x`, then the greedy rule holds at `x` for `s` iff `x` belongs to
the greedy MIS. -/
theorem greedyRule_iff_mem_greedyMIS {x : V} {s : Set V} (hs : G.IsGreedyExcept A r x s) :
    (x ∈ A ∧ ∀ w, G.Adj w x → r w < r x → w ∉ s) ↔ x ∈ G.greedyMIS A r := by
  rw [greedyMIS_iff]
  refine and_congr_right fun _ => forall_congr' fun w => forall_congr' fun _ =>
    forall_congr' fun hw => not_congr (mem_iff_mem_of_lt hs (G.isGreedyExcept_greedyMIS A r x) hw)

/-! ### Congruence -/

open Classical in
/-- The value at `v` only depends on the presence of `v`, its predecessors and their values. -/
theorem partialGreedy_eq_of_preds {G' : SimpleGraph V} {A' : Set V} {r' : V → ℕ} {x v : V}
    (hA : v ∈ A ↔ v ∈ A')
    (hpred : ∀ w, (G.Adj w v ∧ r w < r v) ↔ (G'.Adj w v ∧ r' w < r' v))
    (hval : ∀ w, G.Adj w v → r w < r v →
      G.partialGreedy A r x w = G'.partialGreedy A' r' x w) :
    G.partialGreedy A r x v = G'.partialGreedy A' r' x v := by
  have h3 : (∃ w, r w < r v ∧ G.Adj w v ∧ G.partialGreedy A r x w = some true) ↔
      (∃ w, r' w < r' v ∧ G'.Adj w v ∧ G'.partialGreedy A' r' x w = some true) := by
    refine exists_congr fun w => ⟨fun ⟨hw, hwv, ht⟩ => ?_, fun ⟨hw, hwv, ht⟩ => ?_⟩
    · obtain ⟨a, b⟩ := (hpred w).1 ⟨hwv, hw⟩
      exact ⟨b, a, hval w hwv hw ▸ ht⟩
    · obtain ⟨a, b⟩ := (hpred w).2 ⟨hwv, hw⟩
      exact ⟨b, a, (hval w a b).symm ▸ ht⟩
  have h4 : (∀ w, r w < r v → G.Adj w v → G.partialGreedy A r x w = some false) ↔
      (∀ w, r' w < r' v → G'.Adj w v → G'.partialGreedy A' r' x w = some false) := by
    refine forall_congr' fun w => ⟨fun h hw hwv => ?_, fun h hw hwv => ?_⟩
    · obtain ⟨a, b⟩ := (hpred w).2 ⟨hwv, hw⟩
      exact hval w a b ▸ h b a
    · obtain ⟨a, b⟩ := (hpred w).1 ⟨hwv, hw⟩
      exact (hval w hwv hw).symm ▸ h b a
  rw [partialGreedy_eq G A r x v, partialGreedy_eq G' A' r' x v]
  exact if_congr Iff.rfl rfl (if_congr (not_congr hA) rfl (if_congr h3 rfl (if_congr h4 rfl rfl)))

/-- `partialGreedy` only depends on presence and predecessors of vertices other than `x`. -/
theorem partialGreedy_congr {G' : SimpleGraph V} {A' : Set V} {r' : V → ℕ} {x : V}
    (hA : ∀ v, v ≠ x → (v ∈ A ↔ v ∈ A'))
    (hpred : ∀ v, v ≠ x → ∀ w, (G.Adj w v ∧ r w < r v) ↔ (G'.Adj w v ∧ r' w < r' v)) :
    G.partialGreedy A r x = G'.partialGreedy A' r' x := by
  funext v
  induction v using rank_induction r with
  | h v ih =>
  by_cases hv : v = x
  · subst hv; simp
  exact partialGreedy_eq_of_preds (hA v hv) (hpred v hv) fun w _ hw => ih w hw

/-! ### Moving `x` to the front -/

/-- If `x` is in the greedy MIS, moving `x` to the front of the order does not change the partial
evaluation (in particular the influenced set). -/
theorem partialGreedy_eq_of_moveFirst {r' : V → ℕ} {x : V} (hr : Function.Injective r)
    (hfirst : ∀ v, v ≠ x → r' x < r' v)
    (hord : ∀ u v, u ≠ x → v ≠ x → (r u < r v ↔ r' u < r' v))
    (hx : x ∈ G.greedyMIS A r) :
    G.partialGreedy A r x = G.partialGreedy A r' x := by
  funext v
  induction v using rank_induction r with
  | h v ih =>
  by_cases hv : v = x
  · subst hv; simp
  by_cases hc : G.Adj x v ∧ r v < r x
  · have hvM : v ∉ G.greedyMIS A r := ((G.greedyMIS_iff A r).1 hx).2 v hc.1.symm hc.2
    have hfalse : G.partialGreedy A r x v = some false := by
      rcases hval : G.partialGreedy A r x v with _ | b
      · exact absurd hval (notMem_influenced_of_lt hc.2)
      · have := mem_iff_of_partialGreedy_eq_some (G.isGreedyExcept_greedyMIS A r x) v b hval
        cases b
        · rfl
        · exact absurd (this.2 rfl) hvM
    rw [hfalse, eq_comm, partialGreedy_eq_some_false_iff]
    obtain ⟨-, h | ⟨w, hwv, hw, hwt⟩⟩ := partialGreedy_eq_some_false_iff.1 hfalse
    · exact ⟨hv, Or.inl h⟩
    · have hwx : w ≠ x := by rintro rfl; simp at hwt
      exact ⟨hv, Or.inr ⟨w, hwv, (hord w v hwx hv).1 hw, (ih w hw).symm.trans hwt⟩⟩
  · refine partialGreedy_eq_of_preds Iff.rfl (fun w => ?_) fun w _ hw => ih w hw
    by_cases hw : w = x
    · subst hw
      refine ⟨fun h => ⟨h.1, hfirst v hv⟩, fun h => ⟨h.1, ?_⟩⟩
      exact lt_of_le_of_ne (not_lt.1 fun h' => hc ⟨h.1, h'⟩) (hr.ne (Ne.symm hv))
    · exact and_congr_right fun _ => hord w v hw hv

/-- If a present `x` is not in the greedy MIS, then some vertex before `x` is influenced by `x`
once `x` is moved to the front of the order. -/
theorem exists_mem_influenced_of_notMem {r' : V → ℕ} {x : V}
    (hfirst : ∀ v, v ≠ x → r' x < r' v)
    (hord : ∀ u v, u ≠ x → v ≠ x → (r u < r v ↔ r' u < r' v))
    (hxA : x ∈ A) (hx : x ∉ G.greedyMIS A r) :
    ∃ w, r w < r x ∧ w ∈ G.influenced A r' x := by
  obtain ⟨w, hwM, hwx, hw⟩ := G.greedyMIS_maximal A r hxA hx
  have hwne : w ≠ x := hwx.ne
  refine ⟨w, hw, ?_⟩
  rcases hval : G.partialGreedy A r' x w with _ | b
  · exact hval
  cases b with
  | true =>
    obtain ⟨-, -, h⟩ := partialGreedy_eq_some_true_iff.1 hval
    simpa using h x hwx.symm (hfirst w hwne)
  | false =>
    obtain ⟨-, h | ⟨z, hzw, hz, hzt⟩⟩ := partialGreedy_eq_some_false_iff.1 hval
    · exact absurd (G.greedyMIS_subset A r hwM) h
    have hzx : z ≠ x := by rintro rfl; simp at hzt
    have hA' : ∀ v, v ≠ x → (v ∈ A \ {x} ↔ v ∈ A) := fun v hv => by simp [hv]
    have h1 : z ∈ G.greedyMIS (A \ {x}) r' :=
      (mem_iff_of_partialGreedy_eq_some (G.isGreedyExcept_greedyMIS_of_eqOn A r' hA') z true
        hzt).2 rfl
    have hcongr : G.greedyMIS (A \ {x}) r = G.greedyMIS (A \ {x}) r' :=
      G.greedyMIS_congr_rank _ _ fun u v hu hv _ => hord u v hu.2 hv.2
    rw [← hcongr] at h1
    have hzr : r z < r w := (hord z w hzx hwne).2 hz
    have h2 : z ∈ G.greedyMIS A r :=
      (mem_iff_mem_of_lt (G.isGreedyExcept_greedyMIS_of_eqOn A r hA')
        (G.isGreedyExcept_greedyMIS A r x) (hzr.trans hw)).1 h1
    exact (((G.greedyMIS_iff A r).1 hwM).2 z hzw hzr h2).elim

/-! ### Invariance under reordering -/

/-- With `x` first, a surely-in vertex has no influenced neighbour. -/
theorem notMem_influenced_of_adj {x u w : V} (hr : Function.Injective r)
    (hfirst : ∀ v, v ≠ x → r x < r v) (hu : G.partialGreedy A r x u = some true)
    (hadj : G.Adj w u) : w ∉ G.influenced A r x := by
  obtain ⟨hux, -, hpred⟩ := partialGreedy_eq_some_true_iff.1 hu
  intro hw
  change G.partialGreedy A r x w = none at hw
  rcases lt_or_gt_of_ne (hr.ne hadj.ne) with h | h
  · simp [hpred w hadj h] at hw
  · have hwx : w ≠ x := by rintro rfl; exact lt_asymm h (hfirst u hux)
    have : G.partialGreedy A r x w = some false :=
      partialGreedy_eq_some_false_iff.2 ⟨hwx, Or.inr ⟨u, hadj.symm, h, hu⟩⟩
    simp [this] at hw

/-- **Claims 4 and 5 of Censor-Hillel–Haramaty–Karnin.** With `x` first, the partial evaluation
(hence the influenced set `P`) does not change under a reordering that keeps the relative order
inside `P` and inside its complement. -/
theorem partialGreedy_eq_of_reorder {r₁ r₂ : V → ℕ} {x : V} (hr₁ : Function.Injective r₁)
    (h₁ : ∀ v, v ≠ x → r₁ x < r₁ v) (h₂ : ∀ v, v ≠ x → r₂ x < r₂ v)
    (hord : ∀ u v, u ≠ x → v ≠ x →
      (u ∈ G.influenced A r₁ x ↔ v ∈ G.influenced A r₁ x) → (r₁ u < r₁ v ↔ r₂ u < r₂ v)) :
    G.partialGreedy A r₂ x = G.partialGreedy A r₁ x := by
  -- outside the influenced set
  have hout : ∀ u, u ∉ G.influenced A r₁ x →
      G.partialGreedy A r₂ x u = G.partialGreedy A r₁ x u := by
    intro u
    induction u using rank_induction r₂ with
    | h u ih =>
    intro hu
    have hux : u ≠ x := fun h => hu (h ▸ self_mem_influenced _)
    rcases hval : G.partialGreedy A r₁ x u with _ | b
    · exact absurd hval hu
    cases b with
    | true =>
      obtain ⟨-, huA, hpred⟩ := partialGreedy_eq_some_true_iff.1 hval
      refine partialGreedy_eq_some_true_iff.2 ⟨hux, huA, fun w hwu hw => ?_⟩
      have hwP := notMem_influenced_of_adj hr₁ h₁ hval hwu
      have hwx : w ≠ x := fun h => hwP (h ▸ self_mem_influenced _)
      have hw₁ : r₁ w < r₁ u := (hord w u hwx hux (iff_of_false hwP hu)).2 hw
      rw [ih w hw hwP]
      exact hpred w hwu hw₁
    | false =>
      obtain ⟨-, h | ⟨z, hzu, hz, hzt⟩⟩ := partialGreedy_eq_some_false_iff.1 hval
      · exact partialGreedy_eq_some_false_iff.2 ⟨hux, Or.inl h⟩
      have hzP : z ∉ G.influenced A r₁ x := by
        intro hzP; change _ = none at hzP; simp [hzP] at hzt
      have hzx : z ≠ x := fun h => hzP (h ▸ self_mem_influenced _)
      have hz₂ : r₂ z < r₂ u := (hord z u hzx hux (iff_of_false hzP hu)).1 hz
      exact partialGreedy_eq_some_false_iff.2 ⟨hux, Or.inr ⟨z, hzu, hz₂, (ih z hz₂ hzP).trans hzt⟩⟩
  -- inside the influenced set
  have hin : ∀ u, u ∈ G.influenced A r₁ x → G.partialGreedy A r₂ x u = none := by
    intro u
    induction u using rank_induction r₂ with
    | h u ih =>
    intro hu
    rcases partialGreedy_eq_none_iff.1 hu with rfl | ⟨huA, hnt, w, hwu, hw, hwn⟩
    · simp
    have hux : u ≠ x := by
      rintro rfl
      exact lt_asymm hw (h₁ w (fun h => by subst h; exact lt_irrefl _ hw))
    refine partialGreedy_eq_none_iff.2 (Or.inr ⟨huA, fun z hzu hz hzt => ?_, w, hwu, ?_, ?_⟩)
    · by_cases hzP : z ∈ G.influenced A r₁ x
      · simp [ih z hz hzP] at hzt
      · rw [hout z hzP] at hzt
        exact notMem_influenced_of_adj hr₁ h₁ hzt hzu.symm hu
    · by_cases hwx : w = x
      · subst hwx; exact h₂ u hux
      · exact (hord w u hwx hux (iff_of_true hwn hu)).1 hw
    · have hw₂ : r₂ w < r₂ u := by
        by_cases hwx : w = x
        · subst hwx; exact h₂ u hux
        · exact (hord w u hwx hux (iff_of_true hwn hu)).1 hw
      exact ih w hw₂ hwn
  funext u
  by_cases hu : u ∈ G.influenced A r₁ x
  · rw [hin u hu]; exact hu.symm
  · exact hout u hu

end SimpleGraph
