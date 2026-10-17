/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Topology.UniformSpace.Real
public import Mathlib.Topology.Order.Real

/-!
# Iterative (memoryless) Byzantine approximate consensus on directed graphs

The model of Vaidya–Tseng–Liang (PODC 2012) and of the MSR / W-MSR literature
(LeBlanc–Zhang–Koutsoukos–Sundaram): synchronous rounds on a directed graph `G`, real-valued
states, Byzantine nodes that may send arbitrary and *different* values to different
out-neighbours.

A node `i` has in-neighbours `inNbrs G i = {j | G.Adj j i, j ≠ i}` (self-loops of the `Digraph` are
ignored: every node always "hears" its own state). In iteration `t + 1` every node sends its state
`x t i` on all outgoing links and then replaces its state by `Z i r (x t i)`, where `r` is the
vector of received values (`r j = 0` for `j ∉ inNbrs G i`, so `Z i` cannot see non-neighbours).
There is
**no** round counter and **no** other memory: the state is the output ("output constraint" + "no
sense of time" of the paper).

## Main definitions

* `inNbrs G i` — the in-neighbours of `i` (as a `Finset`, classical).
* `Scenario V` — the adversary's data: faulty set `F`, inputs, and the Byzantine messages
  `adv t j i` (value sent by faulty `j` to `i` in iteration `t + 1`).
* `recv G F m x i` — the vector received by `i` when the states are `x` and faulty nodes send `m`.
* `IterAlg V` — a deterministic iterative algorithm `Z : V → (V → ℝ) → ℝ → ℝ`;
  `IterAlg.run G A S t` its states.
* `IsRun G Step S x` — runs of a *nondeterministic* iterative algorithm (step relation). Used to
  quantify over all tie-breaking rules (even adversarial, time-dependent ones).
* `ValidHull`, `ValidStep`, `Converges` — the validity / convergence requirements;
  `IterAlg.Correct G f A` — correct against every scenario with at most `f` faulty nodes.

## Main results

* `IterAlg.run_add`: no sense of time — the run from time `t` on is a run from the states at `t`.
* `IterAlg.correct_iff_correctStep`: for iterative algorithms, "outputs stay in the convex hull of
  the fault-free inputs" is equivalent to the per-iteration validity (1) of the paper.
* `ValidStep.hull_from`, `ValidStep.exists_tendsto`: with validity (1), convergence
  (`U[t] - μ[t] → 0`) implies that all fault-free states converge to one common limit.
* `IterAlg.localValid`: a correct algorithm's transition function is *locally valid*: if all but at
  most `f` received values and the own value lie in `[lo, hi]`, so does the new state.
-/

@[expose] public section

open Finset

namespace Cslib.ApproxConsensus

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In-neighbours of `i`: the nodes `j ≠ i` with an edge `j → i`. -/
noncomputable def inNbrs (G : Digraph V) (i : V) : Finset V := by
  classical exact univ.filter (fun j => G.Adj j i ∧ j ≠ i)

@[simp] theorem mem_inNbrs {G : Digraph V} {i j : V} : j ∈ inNbrs G i ↔ G.Adj j i ∧ j ≠ i := by
  classical simp [inNbrs]

theorem self_notMem_inNbrs (G : Digraph V) (i : V) : i ∉ inNbrs G i := by simp

/-- The adversary's data. States are computed from it; faulty nodes' own states are meaningless
(they are never read: faulty nodes communicate only through `adv`). -/
structure Scenario (V : Type*) where
  /-- The Byzantine nodes (static). -/
  F : Finset V
  /-- Inputs (initial states). -/
  input : V → ℝ
  /-- `adv t j i`: the value the faulty node `j` sends to `i` in iteration `t + 1`. -/
  adv : ℕ → V → V → ℝ

/-- The vector received by `i` in an iteration where the current states are `x` and faulty nodes
send `m j i` to `i`. Entries of non-in-neighbours are `0` (not visible). -/
noncomputable def recv (G : Digraph V) (F : Finset V) (m : V → V → ℝ) (x : V → ℝ) (i : V) :
    V → ℝ := by
  classical exact fun j => if j ∈ inNbrs G i then (if j ∈ F then m j i else x j) else 0

theorem recv_of_mem {G : Digraph V} {F : Finset V} {m : V → V → ℝ} {x : V → ℝ} {i j : V}
    (hj : j ∈ inNbrs G i) (hjF : j ∉ F) : recv G F m x i j = x j := by
  classical simp [recv, hj, hjF]

theorem recv_of_mem_F {G : Digraph V} {F : Finset V} {m : V → V → ℝ} {x : V → ℝ} {i j : V}
    (hj : j ∈ inNbrs G i) (hjF : j ∈ F) : recv G F m x i j = m j i := by
  classical simp [recv, hj, hjF]

theorem recv_of_notMem {G : Digraph V} {F : Finset V} {m : V → V → ℝ} {x : V → ℝ} {i j : V}
    (hj : j ∉ inNbrs G i) : recv G F m x i j = 0 := by
  classical simp [recv, hj]

/-- A deterministic iterative algorithm: node `i` maps (received vector, own state) to its new
state. It may depend on the topology (it is defined for a fixed graph). -/
structure IterAlg (V : Type*) where
  /-- Transition function `Z i r v`. -/
  Z : V → (V → ℝ) → ℝ → ℝ

/-- States of a run of `A` in scenario `S`: `run 0 = input` and
`run (t+1) i = Z i (received) (run t i)`. -/
noncomputable def IterAlg.run (G : Digraph V) (A : IterAlg V) (S : Scenario V) : ℕ → V → ℝ
  | 0 => S.input
  | t + 1 => fun i => A.Z i (recv G S.F (S.adv t) (IterAlg.run G A S t) i) (IterAlg.run G A S t i)

@[simp] theorem IterAlg.run_zero (G : Digraph V) (A : IterAlg V) (S : Scenario V) :
    A.run G S 0 = S.input := rfl

theorem IterAlg.run_succ (G : Digraph V) (A : IterAlg V) (S : Scenario V) (t : ℕ) (i : V) :
    A.run G S (t + 1) i = A.Z i (recv G S.F (S.adv t) (A.run G S t) i) (A.run G S t i) := rfl

/-- The scenario "restarted" at time `t` from states `x`. -/
def Scenario.shift (S : Scenario V) (t : ℕ) (x : V → ℝ) : Scenario V :=
  ⟨S.F, x, fun s => S.adv (t + s)⟩

/-- No sense of time: running `A` from the states at time `t` (with the remaining adversary
messages) continues the original run. -/
theorem IterAlg.run_add (G : Digraph V) (A : IterAlg V) (S : Scenario V) (t s : ℕ) :
    A.run G (S.shift t (A.run G S t)) s = A.run G S (t + s) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    funext i
    rw [IterAlg.run_succ, ih, ← Nat.add_assoc, IterAlg.run_succ]
    rfl

/-- Runs of a nondeterministic iterative algorithm given by a step relation
`Step i r v v'` (`v'` is a possible new state of `i` with received vector `r` and state `v`).
Faulty nodes' entries of `x` are unconstrained (and never read). -/
def IsRun (G : Digraph V) (Step : V → (V → ℝ) → ℝ → ℝ → Prop) (S : Scenario V)
    (x : ℕ → V → ℝ) : Prop :=
  x 0 = S.input ∧ ∀ t, ∀ i ∉ S.F, Step i (recv G S.F (S.adv t) (x t) i) (x t i) (x (t + 1) i)

/-- The step relation of a deterministic algorithm. -/
def IterAlg.toStep (A : IterAlg V) : V → (V → ℝ) → ℝ → ℝ → Prop :=
  fun i r v v' => v' = A.Z i r v

theorem IterAlg.isRun_run (G : Digraph V) (A : IterAlg V) (S : Scenario V) :
    IsRun G A.toStep S (A.run G S) :=
  ⟨rfl, fun _ _ _ => rfl⟩

/-- Validity (the paper's primary formulation): every fault-free output lies in the convex hull of
the fault-free inputs, `μ[0] ≤ v_i[t] ≤ U[0]`. -/
def ValidHull (F : Finset V) (x : ℕ → V → ℝ) : Prop :=
  ∀ t, ∀ i ∉ F, (∃ j ∉ F, x 0 j ≤ x t i) ∧ (∃ k ∉ F, x t i ≤ x 0 k)

/-- Validity (1) of the paper: `μ[t-1] ≤ v_i[t] ≤ U[t-1]` for every iteration `t`. -/
def ValidStep (F : Finset V) (x : ℕ → V → ℝ) : Prop :=
  ∀ t, ∀ i ∉ F, (∃ j ∉ F, x t j ≤ x (t + 1) i) ∧ (∃ k ∉ F, x (t + 1) i ≤ x t k)

/-- Convergence: `U[t] - μ[t] → 0`, i.e. the fault-free states get arbitrarily close. -/
def Converges (F : Finset V) (x : ℕ → V → ℝ) : Prop :=
  ∀ ε > 0, ∃ T, ∀ t ≥ T, ∀ i ∉ F, ∀ j ∉ F, |x t i - x t j| ≤ ε

/-- `A` solves iterative approximate Byzantine consensus on `G` against `f` faults (validity as
convex hull of the fault-free inputs). -/
def IterAlg.Correct (G : Digraph V) (f : ℕ) (A : IterAlg V) : Prop :=
  ∀ S : Scenario V, #S.F ≤ f → ValidHull S.F (A.run G S) ∧ Converges S.F (A.run G S)

/-- Same, with the per-iteration validity condition (1) of the paper. -/
def IterAlg.CorrectStep (G : Digraph V) (f : ℕ) (A : IterAlg V) : Prop :=
  ∀ S : Scenario V, #S.F ≤ f → ValidStep S.F (A.run G S) ∧ Converges S.F (A.run G S)

omit [Fintype V] [DecidableEq V] in
/-- Per-iteration validity implies convex-hull validity (by induction on time). -/
theorem ValidStep.validHull {F : Finset V} {x : ℕ → V → ℝ} (h : ValidStep F x) :
    ValidHull F x := by
  intro t
  induction t with
  | zero => intro i hi; exact ⟨⟨i, hi, le_rfl⟩, ⟨i, hi, le_rfl⟩⟩
  | succ t ih =>
    intro i hi
    obtain ⟨⟨j, hj, h1⟩, ⟨k, hk, h2⟩⟩ := h t i hi
    obtain ⟨⟨j', hj', h3⟩, -⟩ := ih j hj
    obtain ⟨-, ⟨k', hk', h4⟩⟩ := ih k hk
    exact ⟨⟨j', hj', h3.trans h1⟩, ⟨k', hk', h2.trans h4⟩⟩

omit [Fintype V] [DecidableEq V] in
/-- Per-iteration validity confines the states at any later time to the hull at time `t`. -/
theorem ValidStep.hull_from {F : Finset V} {x : ℕ → V → ℝ} (h : ValidStep F x) (t d : ℕ) :
    ∀ i ∉ F, (∃ j ∉ F, x t j ≤ x (t + d) i) ∧ (∃ k ∉ F, x (t + d) i ≤ x t k) := by
  induction d with
  | zero => intro i hi; exact ⟨⟨i, hi, le_rfl⟩, ⟨i, hi, le_rfl⟩⟩
  | succ d ih =>
    intro i hi
    obtain ⟨⟨j, hj, h1⟩, ⟨k, hk, h2⟩⟩ := h (t + d) i hi
    obtain ⟨⟨j', hj', h3⟩, -⟩ := ih j hj
    obtain ⟨-, ⟨k', hk', h4⟩⟩ := ih k hk
    exact ⟨⟨j', hj', h3.trans h1⟩, ⟨k', hk', h2.trans h4⟩⟩

omit [Fintype V] [DecidableEq V] in
/-- Validity (1) and convergence (`U[t] - μ[t] → 0`) imply that all fault-free states converge to
one common limit ("the outputs converge to an identical value"). -/
theorem ValidStep.exists_tendsto {F : Finset V} {x : ℕ → V → ℝ} (hv : ValidStep F x)
    (hc : Converges F x) :
    ∃ c, ∀ i ∉ F, Filter.Tendsto (fun t => x t i) Filter.atTop (nhds c) := by
  by_cases hF : ∃ i₀, i₀ ∉ F
  · obtain ⟨i₀, hi₀⟩ := hF
    have hcs : CauchySeq (fun t => x t i₀) := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨T, hT⟩ := hc (ε / 2) (by linarith)
      refine ⟨T, fun n hn => ?_⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
      obtain ⟨⟨j, hj, h1⟩, ⟨k, hk, h2⟩⟩ := hv.hull_from T d i₀ hi₀
      have a1 := hT T le_rfl j hj i₀ hi₀
      have a2 := hT T le_rfl k hk i₀ hi₀
      rw [Real.dist_eq, abs_lt]
      rw [abs_le] at a1 a2
      constructor <;> linarith
    obtain ⟨c, hcl⟩ := cauchySeq_tendsto_of_complete hcs
    refine ⟨c, fun i hi => tendsto_of_tendsto_of_dist hcl ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T, hT⟩ := hc (ε / 2) (by linarith)
    refine ⟨T, fun n hn => ?_⟩
    rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_abs]
    linarith [hT n hn i₀ hi₀ i hi]
  · push Not at hF
    exact ⟨0, fun i hi => absurd (hF i) hi⟩

/-- For iterative algorithms the two validity notions coincide (the paper's remark that, without
a sense of time, validity becomes (1)). -/
theorem IterAlg.correct_iff_correctStep (G : Digraph V) (f : ℕ) (A : IterAlg V) :
    A.Correct G f ↔ A.CorrectStep G f := by
  constructor
  · intro h S hS
    refine ⟨fun t i hi => ?_, (h S hS).2⟩
    have := (h (S.shift t (A.run G S t)) hS).1 1 i hi
    simp only [IterAlg.run_add, Nat.add_zero] at this
    exact this
  · intro h S hS
    exact ⟨(h S hS).1.validHull, (h S hS).2⟩

/-- **Local validity.** If `A` is correct, then whenever all received values outside a set
`B ⊆ inNbrs G i` of at most `f` (suspected) nodes, and the own state, lie in `[lo, hi]`, the new
state lies in `[lo, hi]`. (Proof: an execution in which `B` is the faulty set and all other
non-neighbours start in `[lo, hi]` is indistinguishable for `i`.) -/
theorem IterAlg.localValid {G : Digraph V} {f : ℕ} {A : IterAlg V} (hA : A.Correct G f)
    (i : V) (r : V → ℝ) (v lo hi : ℝ) (B : Finset V) (hB : B ⊆ inNbrs G i) (hBf : #B ≤ f)
    (hv : lo ≤ v ∧ v ≤ hi) (hr : ∀ j ∈ inNbrs G i, j ∉ B → lo ≤ r j ∧ r j ≤ hi)
    (hr0 : ∀ j ∉ inNbrs G i, r j = 0) :
    lo ≤ A.Z i r v ∧ A.Z i r v ≤ hi := by
  classical
  let S : Scenario V := ⟨B, fun j => if j ∈ inNbrs G i ∧ j ∉ B then r j else v,
    fun _ j _ => r j⟩
  have hiB : i ∉ B := fun h => self_notMem_inNbrs G i (hB h)
  have hrecv : recv G S.F (S.adv 0) (A.run G S 0) i = r := by
    funext j
    by_cases hj : j ∈ inNbrs G i
    · by_cases hjB : j ∈ B
      · rw [recv_of_mem_F hj hjB]
      · rw [recv_of_mem hj hjB]
        simp only [IterAlg.run_zero, S, hj, hjB, not_false_eq_true, and_self, ↓reduceIte]
    · rw [recv_of_notMem hj, hr0 j hj]
  have hval : ∀ j ∉ B, lo ≤ S.input j ∧ S.input j ≤ hi := by
    intro j hj
    by_cases h : j ∈ inNbrs G i
    · simp only [S, h, hj, not_false_eq_true, and_self, ↓reduceIte]; exact hr j h hj
    · simp only [S, h, false_and, ↓reduceIte]; exact hv
  have hvi : S.input i = v := by simp [S]
  obtain ⟨⟨j, hj, h1⟩, ⟨k, hk, h2⟩⟩ := (hA S hBf).1 1 i hiB
  rw [IterAlg.run_succ, hrecv] at h1 h2
  simp only [IterAlg.run_zero, hvi] at h1 h2
  exact ⟨(hval j hj).1.trans h1, h2.trans (hval k hk).2⟩

end Cslib.ApproxConsensus
