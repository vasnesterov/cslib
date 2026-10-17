/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Relation
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push

/-!
# Stabilization and global fairness for transition systems

Generic notions for a transition relation `R : X → X → Prop` on configurations `X`, used by
population protocols and other self-stabilizing systems whose executions are runs of `R`
(an adversarial scheduler is a choice of run, a random scheduler is a Markov kernel supported on
`R`, see `SelfStabilization/Markov.lean`).

## Main definitions

* `Reach R`: reachability, the reflexive-transitive closure of `R`.
* `IsTrap R S`: the set `S` is a trap, i.e. closed under transitions.
* `StablyIn R S x`: every configuration reachable from `x` lies in `S`.
* `SelfStabilizes R S`: from every configuration, a configuration stably in `S` is reachable.
* `IsSilent R x`: every transition from `x` is a self-loop.
* `Run R`: an infinite run; `Run.GloballyFair` is global fairness in the sense of Angluin et al.:
  if `x` occurs infinitely often and `R x y`, then `y` occurs infinitely often.

## Main results

* `selfStabilizes_iff_of_isTrap`: for a closed set, self-stabilization is reachability of `S`.
* `Run.GloballyFair.eventually_mem`: with finitely many configurations, a globally fair run
  eventually enters (and stays in) a closed set reachable from all reachable configurations.
* `exists_globallyFair`: a finite total transition system has a globally fair run from every
  configuration (round-robin over successors). This is the non-vacuity fact needed to *refute*
  fairness-based correctness claims (`exists_globallyFair_forall_not_mem`).
* `globallyFair_iff_reach`: for a closed set `S` in a finite total system, "every globally fair run
  eventually enters `S`" iff "`S` is reachable from every configuration".

## References

* [D. Angluin, J. Aspnes, Z. Diamadi, M. J. Fischer, R. Peralta, *Computation in networks of
  passively mobile finite-state sensors*][Angluin2006]
-/

@[expose] public section

open Filter

namespace Cslib.TransitionSystem

variable {X : Type*} (R : X → X → Prop)

/-- Reachability: the reflexive-transitive closure of the transition relation. -/
abbrev Reach : X → X → Prop := Relation.ReflTransGen R

/-- A set of configurations is a *trap* (closed under transitions) if every transition from it
stays in it. -/
def IsTrap (S : Set X) : Prop := ∀ ⦃x y⦄, x ∈ S → R x y → y ∈ S

/-- `x` is *stably in* `S`: every configuration reachable from `x` lies in `S`. -/
def StablyIn (S : Set X) (x : X) : Prop := ∀ y, Reach R x y → y ∈ S

/-- The system *self-stabilizes* to `S`: from every configuration, some configuration that is
stably in `S` is reachable. For finitely many configurations this is equivalent to stabilization
under global fairness (`globallyFair_iff_reach`) and with probability `1` under every random
scheduler supported on the transitions (`SelfStabilizes.tendsto`). -/
def SelfStabilizes (S : Set X) : Prop := ∀ x, ∃ y, Reach R x y ∧ StablyIn R S y

/-- A configuration is *silent* if every transition from it is a self-loop. -/
def IsSilent (x : X) : Prop := ∀ y, R x y → y = x

/-- An infinite run of the transition system. -/
structure Run where
  /-- The configuration at time `t`. -/
  st : ℕ → X
  /-- Consecutive configurations are related by a transition. -/
  step : ∀ t, R (st t) (st (t + 1))

variable {R}

/-- Global fairness: every transition from a configuration that occurs infinitely often is taken
infinitely often, i.e. its target occurs infinitely often. -/
def Run.GloballyFair (E : Run R) : Prop :=
  ∀ x y, R x y → (∃ᶠ t in atTop, E.st t = x) → ∃ᶠ t in atTop, E.st t = y

variable {S T : Set X} {x y : X}

/-! ### Closed sets, stability, silence -/

/-- A closed set is closed under reachability. -/
theorem IsTrap.reach (hS : IsTrap R S) (hx : x ∈ S) (h : Reach R x y) : y ∈ S := by
  induction h with
  | refl => exact hx
  | tail _ hst ih => exact hS ih hst

/-- A configuration stably in `S` is in `S`. -/
theorem StablyIn.mem (h : StablyIn R S x) : x ∈ S := h x .refl

/-- Stability is preserved along runs. -/
theorem StablyIn.reach (h : StablyIn R S x) (hxy : Reach R x y) : StablyIn R S y :=
  fun z hz => h z (hxy.trans hz)

/-- Stability is monotone in the set. -/
theorem StablyIn.mono (h : StablyIn R S x) (hST : S ⊆ T) : StablyIn R T x :=
  fun z hz => hST (h z hz)

/-- The configurations stably in `S` form a closed set. -/
theorem isTrap_stablyIn : IsTrap R {x | StablyIn R S x} :=
  fun _ _ hx hxy => StablyIn.reach hx (.single hxy)

/-- For a closed set, being stably in it is being in it. -/
theorem IsTrap.stablyIn_iff (hS : IsTrap R S) : StablyIn R S x ↔ x ∈ S :=
  ⟨StablyIn.mem, fun hx _ h => hS.reach hx h⟩

/-- A silent configuration only reaches itself. -/
theorem IsSilent.reach_eq (h : IsSilent R x) (hxy : Reach R x y) : y = x := by
  induction hxy with
  | refl => rfl
  | tail _ hst ih => subst ih; exact h _ hst

/-- A silent configuration in `S` is stably in `S`. -/
theorem IsSilent.stablyIn (h : IsSilent R x) (hx : x ∈ S) : StablyIn R S x :=
  fun _ hy => (h.reach_eq hy).symm ▸ hx

/-- Self-stabilization is monotone in the set. -/
theorem SelfStabilizes.mono (h : SelfStabilizes R S) (hST : S ⊆ T) : SelfStabilizes R T :=
  fun x => (h x).imp fun _ hy => ⟨hy.1, hy.2.mono hST⟩

/-- For a closed set, self-stabilization is reachability of the set from everywhere. -/
theorem selfStabilizes_iff_of_isTrap (hS : IsTrap R S) :
    SelfStabilizes R S ↔ ∀ x, ∃ y ∈ S, Reach R x y :=
  ⟨fun h x => (h x).imp fun _ hy => ⟨hy.2.mem, hy.1⟩,
    fun h x => (h x).imp fun _ hy => ⟨hy.2, hS.stablyIn_iff.2 hy.1⟩⟩

/-- **Detect error and random change.** If from every configuration outside `S` either `S` or an
"error" configuration is reachable, and `S` is reachable from every error configuration, then `S`
is reachable from every configuration. -/
theorem exists_reach_of_err {err : Set X} (herr : ∀ x ∈ err, ∃ y ∈ S, Reach R x y)
    (hcases : ∀ x ∉ S, (∃ y ∈ err, Reach R x y) ∨ ∃ y ∈ S, Reach R x y) (x : X) :
    ∃ y ∈ S, Reach R x y := by
  by_cases hx : x ∈ S
  · exact ⟨x, hx, .refl⟩
  · rcases hcases x hx with ⟨y, hy, hxy⟩ | h
    · obtain ⟨z, hz, hyz⟩ := herr y hy
      exact ⟨z, hz, hxy.trans hyz⟩
    · exact h

/-! ### Runs and global fairness -/

namespace Run

variable (E : Run R)

/-- Later configurations of a run are reachable from earlier ones. -/
theorem reach_of_le {s t : ℕ} (h : s ≤ t) : Reach R (E.st s) (E.st t) := by
  induction t, h using Nat.le_induction with
  | base => exact .refl
  | succ t _ ih => exact ih.tail (E.step t)

/-- Every configuration of a run is reachable from its initial configuration. -/
theorem reach (t : ℕ) : Reach R (E.st 0) (E.st t) := E.reach_of_le t.zero_le

end Run

/-- With finitely many configurations, some configuration occurs infinitely often in every
sequence. -/
theorem exists_frequently_eq [Finite X] (f : ℕ → X) : ∃ x, ∃ᶠ t in atTop, f t = x := by
  obtain ⟨x, hx⟩ := Finite.exists_infinite_fiber f
  exact ⟨x, Nat.frequently_atTop_iff_infinite.2 (Set.infinite_coe_iff.1 hx)⟩

/-- Global fairness with "infinitely often" spelled out. -/
theorem Run.globallyFair_iff {E : Run R} : E.GloballyFair ↔
    ∀ x y, R x y → (∀ T, ∃ t ≥ T, E.st t = x) → ∀ T, ∃ t ≥ T, E.st t = y := by
  simp only [Run.GloballyFair, frequently_atTop, ge_iff_le]

namespace Run.GloballyFair

variable {E : Run R} (hE : E.GloballyFair)
include hE

/-- Under global fairness, every configuration reachable from one occurring infinitely often also
occurs infinitely often. -/
theorem frequently_of_reach (hx : ∃ᶠ t in atTop, E.st t = x) (h : Reach R x y) :
    ∃ᶠ t in atTop, E.st t = y := by
  induction h with
  | refl => exact hx
  | tail _ hst ih => exact hE _ _ hst ih

/-- Under global fairness (finitely many configurations), a configuration reachable from every
configuration reachable from the start is reached. -/
theorem exists_eq [Finite X] (hy : ∀ x, Reach R (E.st 0) x → Reach R x y) : ∃ t, E.st t = y := by
  obtain ⟨x, hx⟩ := exists_frequently_eq E.st
  obtain ⟨t, -, ht⟩ := frequently_atTop.1 hx 0
  exact (hE.frequently_of_reach hx (hy x (ht ▸ E.reach t))).exists

/-- Under global fairness (finitely many configurations): if from every configuration reachable
from the start some configuration of a closed set `S` is reachable, then the run eventually
enters `S` and stays there forever. -/
theorem eventually_mem [Finite X] (hS : IsTrap R S)
    (h : ∀ x, Reach R (E.st 0) x → ∃ y ∈ S, Reach R x y) : ∀ᶠ t in atTop, E.st t ∈ S := by
  obtain ⟨x, hx⟩ := exists_frequently_eq E.st
  obtain ⟨t₀, -, ht₀⟩ := frequently_atTop.1 hx 0
  obtain ⟨y, hyS, hxy⟩ := h x (ht₀ ▸ E.reach t₀)
  obtain ⟨t, ht⟩ := (hE.frequently_of_reach hx hxy).exists
  exact eventually_atTop.2 ⟨t, fun s hs => hS.reach (ht ▸ hyS) (E.reach_of_le hs)⟩

end Run.GloballyFair

/-! ### Existence of globally fair runs: round robin over successors -/

namespace RoundRobin

variable [Fintype X] [DecidableEq X] [DecidableRel R] (htot : ∀ x, ∃ y, R x y) (x₀ : X)

/-- The successors of `x`, as a list. -/
noncomputable def succList (R : X → X → Prop) [DecidableRel R] (x : X) : List X :=
  (Finset.univ.filter (R x)).toList

omit [DecidableEq X] in
/-- The successor list lists exactly the successors. -/
theorem mem_succList {x y : X} : y ∈ succList R x ↔ R x y := by
  simp [succList]

/-- Round-robin choice: the `m`-th visit of `x` moves to the `(m mod #succ)`-th successor. -/
noncomputable def next (x : X) (m : ℕ) : X :=
  (succList R x).get ⟨m % (succList R x).length, Nat.mod_lt _ (by
    obtain ⟨y, hy⟩ := htot x
    exact List.length_pos_of_mem (mem_succList.2 hy))⟩

/-- The run together with the visit counters. -/
noncomputable def aux : ℕ → X × (X → ℕ)
  | 0 => (x₀, fun _ => 0)
  | t + 1 =>
    let p := aux t
    (next htot p.1 (p.2 p.1), Function.update p.2 p.1 (p.2 p.1 + 1))

/-- Number of visits to `y` before time `t`. -/
noncomputable def cnt (t : ℕ) (y : X) : ℕ :=
  ((Finset.range t).filter fun s => (aux htot x₀ s).1 = y).card

private theorem aux_snd (t : ℕ) : (aux htot x₀ t).2 = cnt htot x₀ t := by
  induction t with
  | zero => funext y; simp [aux, cnt]
  | succ t ih =>
    funext y
    simp only [aux, cnt, Finset.range_add_one, Finset.filter_insert]
    rw [ih]
    by_cases hy : (aux htot x₀ t).1 = y
    · subst hy
      rw [ite_eq_left rfl, Finset.card_insert_of_notMem (by simp)]
      simp [cnt]
    · rw [ite_eq_right hy, Function.update_of_ne (Ne.symm hy)]
      rfl

private theorem cnt_succ (t : ℕ) (y : X) :
    cnt htot x₀ (t + 1) y = cnt htot x₀ t y + if (aux htot x₀ t).1 = y then 1 else 0 := by
  simp only [cnt, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

private theorem cnt_mono {s t : ℕ} (h : s ≤ t) (y : X) : cnt htot x₀ s y ≤ cnt htot x₀ t y := by
  induction t, h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => rw [cnt_succ]; omega

/-- The round-robin run. -/
noncomputable def run : Run R where
  st t := (aux htot x₀ t).1
  step _ := mem_succList.1 (List.get_mem _ _)

/-- The round-robin run is globally fair. -/
theorem run_globallyFair : (run htot x₀).GloballyFair := by
  intro x y hxy hx
  rw [frequently_atTop] at hx ⊢
  intro T
  -- the visit counter of `x` is unbounded
  have hunb : ∀ M, ∃ t, M ≤ cnt htot x₀ t x := by
    intro M
    induction M with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ M ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨s, hs, hsx⟩ := hx t
      refine ⟨s + 1, ?_⟩
      have hsx' : (aux htot x₀ s).1 = x := hsx
      rw [cnt_succ, ite_eq_left hsx']
      have := cnt_mono htot x₀ hs x
      omega
  -- every value of the counter is attained at a visit
  have hvisit : ∀ m, ∃ t, (aux htot x₀ t).1 = x ∧ cnt htot x₀ t x = m := by
    intro m
    have hex : ∃ t, m < cnt htot x₀ t x := by
      obtain ⟨t, ht⟩ := hunb (m + 1); exact ⟨t, by omega⟩
    classical
    let t := Nat.find hex
    have ht : m < cnt htot x₀ t x := Nat.find_spec hex
    have ht0 : t ≠ 0 := by
      intro h0
      rw [show t = 0 from h0] at ht
      simp [cnt] at ht
    obtain ⟨t', ht'⟩ := Nat.exists_eq_succ_of_ne_zero ht0
    have hle : cnt htot x₀ t' x ≤ m := by
      have := Nat.find_min hex (show t' < t by omega)
      omega
    rw [ht', cnt_succ] at ht
    refine ⟨t', ?_, ?_⟩
    · by_contra hne; rw [ite_eq_right hne] at ht; omega
    · split_ifs at ht <;> omega
  -- position of `y` in the successor list
  obtain ⟨j, hj⟩ := List.get_of_mem (mem_succList.2 hxy)
  have hjl : (j : ℕ) < (succList R x).length := j.2
  obtain ⟨t, htx, htm⟩ := hvisit (cnt htot x₀ T x * (succList R x).length + j)
  refine ⟨t + 1, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have h1 : cnt htot x₀ (t + 1) x ≤ cnt htot x₀ T x := cnt_mono htot x₀ (by omega) x
    rw [cnt_succ, ite_eq_left htx, htm] at h1
    nlinarith
  · change (aux htot x₀ (t + 1)).1 = y
    simp only [aux]
    rw [aux_snd, htx, htm, ← hj]
    simp only [next]
    congr 1
    ext
    simp only
    rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hjl]

end RoundRobin

/-- **Globally fair runs exist.** A finite transition system in which every configuration has a
successor has a globally fair run from every configuration. -/
theorem exists_globallyFair [Finite X] (htot : ∀ x, ∃ y, R x y) (x₀ : X) :
    ∃ E : Run R, E.st 0 = x₀ ∧ E.GloballyFair := by
  classical
  have := Fintype.ofFinite X
  exact ⟨RoundRobin.run htot x₀, rfl, RoundRobin.run_globallyFair htot x₀⟩

/-- If no configuration of `S` is reachable from `x₀`, some globally fair run from `x₀` never
visits `S` (finite total systems). -/
theorem exists_globallyFair_forall_not_mem [Finite X] (htot : ∀ x, ∃ y, R x y) {x₀ : X}
    (h : ∀ y, Reach R x₀ y → y ∉ S) :
    ∃ E : Run R, E.st 0 = x₀ ∧ E.GloballyFair ∧ ∀ t, E.st t ∉ S := by
  obtain ⟨E, hE0, hE⟩ := exists_globallyFair htot x₀
  exact ⟨E, hE0, hE, fun t => h _ (hE0 ▸ E.reach t)⟩

/-- For a closed set `S` in a finite total transition system: every globally fair run eventually
enters `S` iff `S` is reachable from every configuration. -/
theorem globallyFair_iff_reach [Finite X] (htot : ∀ x, ∃ y, R x y) (hS : IsTrap R S) :
    (∀ E : Run R, E.GloballyFair → ∃ t, E.st t ∈ S) ↔ ∀ x, ∃ y ∈ S, Reach R x y := by
  refine ⟨fun h x => ?_, fun h E hE => (hE.eventually_mem hS fun x _ => h x).exists⟩
  obtain ⟨E, hE0, hE⟩ := exists_globallyFair htot x
  obtain ⟨t, ht⟩ := h E hE
  exact ⟨E.st t, ht, hE0 ▸ E.reach t⟩

end Cslib.TransitionSystem
