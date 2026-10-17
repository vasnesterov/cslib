/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Foundations.Data.Nat.Descent
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify

/-!
# The Stone Age (SA) model with an asynchronous scheduler

The stone age model of Emek and Wattenhofer (PODC 2013), in the simplified form used by
Emek–Keren (PODC 2021): anonymous finite-state nodes of a graph `G`; a node senses the *set* of
states present in its closed neighbourhood `N⁺(v)` (it can neither count nor identify neighbours).
An adversarial schedule activates a set `A t ⊆ V` of nodes at each time `t`; activated nodes apply
the (common) transition function to their state and their signal, the others keep their state.

We formalize the deterministic variant (transition function `Q → Set Q → Q`).

## Main definitions

* `StoneAge.Algorithm Q`: a deterministic SA algorithm.
* `StoneAge.signal G C v`: the set of states sensed by `v` under configuration `C`.
* `StoneAge.step`, `StoneAge.run`, `StoneAge.IsRun`: executions under a schedule `A : ℕ → Set V`.
* `StoneAge.Fair A`: no node starvation (every node is activated infinitely often).
* `StoneAge.rho A t`: the round operator `ϱ(t)` — the earliest time such that every node is
  activated in `[t, ϱ(t))`; `StoneAge.R A i = ϱ^i(0)`.

## Main results

* `rho_spec`, `rho_le_of_covered`, `rho_mono`, `rho_iter_mono`, `lt_rho`.
* Non-vacuity: the synchronous schedule (`fair_sync`, `rho_sync`) and round-robin schedules
  (`fair_roundRobin`, `rho_roundRobin_le`) are fair.
-/

@[expose] public section

namespace Cslib.StoneAge

variable {V Q : Type*}

/-- A deterministic stone-age algorithm: the new state of an activated node is a function of its
current state and the set of states it senses in its closed neighbourhood. -/
structure Algorithm (Q : Type*) where
  /-- The transition function. -/
  δ : Q → Set Q → Q

variable (G : SimpleGraph V)

/-- The signal of `v` under `C`: the set of states sensed in the inclusive neighbourhood of `v`. -/
def signal (C : V → Q) (v : V) : Set Q := {q | ∃ u, (u = v ∨ G.Adj v u) ∧ C u = q}

theorem mem_signal {C : V → Q} {v : V} {q : Q} :
    q ∈ signal G C v ↔ ∃ u, (u = v ∨ G.Adj v u) ∧ C u = q := Iff.rfl

theorem self_mem_signal (C : V → Q) (v : V) : C v ∈ signal G C v := ⟨v, Or.inl rfl, rfl⟩

theorem mem_signal_of_adj (C : V → Q) {v u : V} (h : G.Adj v u) : C u ∈ signal G C v :=
  ⟨u, Or.inr h, rfl⟩

/-- `∀ q ∈ signal`, unfolded to the closed neighbourhood. -/
theorem forall_mem_signal {C : V → Q} {v : V} {p : Q → Prop} :
    (∀ q ∈ signal G C v, p q) ↔ p (C v) ∧ ∀ u, G.Adj v u → p (C u) := by
  constructor
  · intro h
    exact ⟨h _ (self_mem_signal G C v), fun u hu => h _ (mem_signal_of_adj G C hu)⟩
  · rintro ⟨h1, h2⟩ q ⟨u, hu | hu, rfl⟩
    · subst hu; exact h1
    · exact h2 u hu

open Classical in
/-- One step: activated nodes apply the transition function, the others keep their state. -/
noncomputable def step (P : Algorithm Q) (A : Set V) (C : V → Q) : V → Q :=
  fun v => if v ∈ A then P.δ (C v) (signal G C v) else C v

/-- The execution from the initial configuration `C0` under schedule `A`. -/
noncomputable def run (P : Algorithm Q) (C0 : V → Q) (A : ℕ → Set V) : ℕ → V → Q
  | 0 => C0
  | t + 1 => step G P (A t) (run P C0 A t)

/-- `C` is an execution of `P` under schedule `A` (from the initial configuration `C 0`). -/
def IsRun (P : Algorithm Q) (A : ℕ → Set V) (C : ℕ → V → Q) : Prop :=
  ∀ t, C (t + 1) = step G P (A t) (C t)

theorem isRun_run (P : Algorithm Q) (C0 : V → Q) (A : ℕ → Set V) :
    IsRun G P A (run G P C0 A) := fun _ => rfl

theorem run_zero (P : Algorithm Q) (C0 : V → Q) (A : ℕ → Set V) : run G P C0 A 0 = C0 := rfl

variable {G}

namespace IsRun

variable {P : Algorithm Q} {A : ℕ → Set V} {C : ℕ → V → Q}

theorem succ_of_mem (hC : IsRun G P A C) {t : ℕ} {v : V} (hv : v ∈ A t) :
    C (t + 1) v = P.δ (C t v) (signal G (C t) v) := by
  classical
  rw [hC t]; simp [step, hv]

theorem succ_of_not_mem (hC : IsRun G P A C) {t : ℕ} {v : V} (hv : v ∉ A t) :
    C (t + 1) v = C t v := by
  classical
  rw [hC t]; simp [step, hv]

/-- A state change requires an activation. -/
theorem mem_of_ne (hC : IsRun G P A C) {t : ℕ} {v : V} (h : C (t + 1) v ≠ C t v) : v ∈ A t := by
  by_contra hv; exact h (hC.succ_of_not_mem hv)

/-- A node that is not activated during `[t, t')` keeps its state. -/
theorem eq_of_not_mem (hC : IsRun G P A C) {t t' : ℕ} {v : V} (htt' : t ≤ t')
    (h : ∀ s, t ≤ s → s < t' → v ∉ A s) : C t' v = C t v := by
  induction t', htt' using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [hC.succ_of_not_mem (h n hn (Nat.lt_succ_self n)), ih fun s h1 h2 => h s h1 (by omega)]

/-- Shifting an execution in time gives an execution. -/
theorem shift (hC : IsRun G P A C) (T : ℕ) : IsRun G P (fun t => A (T + t)) (fun t => C (T + t)) :=
  fun t => hC (T + t)

end IsRun

/-! ## Induction over time intervals (deprecated aliases, see `Nat.Icc_induction_down`) -/

@[deprecated (since := "2026-10-18")] alias back_induction := Nat.Icc_induction_down
@[deprecated (since := "2026-10-18")] alias fwd_induction := Nat.Icc_induction_up
@[deprecated (since := "2026-10-18")] alias exists_first := Nat.exists_first_Ioc

/-! ## Fairness and the round operator -/

/-- No node starvation: every node is activated infinitely often. -/
def Fair (A : ℕ → Set V) : Prop := ∀ v t, ∃ s, t ≤ s ∧ v ∈ A s

/-- Every node is activated at some time in `[t, t')`. -/
def Covered (A : ℕ → Set V) (t t' : ℕ) : Prop := ∀ v, ∃ s, t ≤ s ∧ s < t' ∧ v ∈ A s

theorem Fair.exists_covered [Finite V] {A : ℕ → Set V} (hA : Fair A) (t : ℕ) :
    ∃ t', Covered A t t' := by
  choose f hf using fun v => hA v t
  cases nonempty_fintype V
  refine ⟨Finset.univ.sup f + 1, fun v => ⟨f v, (hf v).1, ?_, (hf v).2⟩⟩
  have := Finset.le_sup (f := f) (Finset.mem_univ v)
  omega

theorem Covered.mono {A : ℕ → Set V} {t t' s s' : ℕ} (h : Covered A t t') (hs : s ≤ t)
    (hs' : t' ≤ s') : Covered A s s' := fun v => by
  obtain ⟨r, h1, h2, h3⟩ := h v; exact ⟨r, by omega, by omega, h3⟩

open Classical in
/-- The round operator `ϱ(t)`: the earliest time `t'` such that every node is activated in
`[t, t')` (defined as `t` if there is no such time, which cannot happen for fair schedules on
finite graphs). -/
noncomputable def rho (A : ℕ → Set V) (t : ℕ) : ℕ :=
  if h : ∃ t', t ≤ t' ∧ Covered A t t' then Nat.find h else t

/-- `R(i) = ϱ^i(0)`. -/
noncomputable def R (A : ℕ → Set V) (i : ℕ) : ℕ := (rho A)^[i] 0

section Rho

variable [Finite V] {A : ℕ → Set V}

theorem Fair.exists_le_covered (hA : Fair A) (t : ℕ) : ∃ t', t ≤ t' ∧ Covered A t t' := by
  obtain ⟨t', h⟩ := hA.exists_covered t
  exact ⟨max t t', le_max_left _ _, h.mono le_rfl (le_max_right _ _)⟩

theorem rho_spec (hA : Fair A) (t : ℕ) : Covered A t (rho A t) := by
  classical
  have h := hA.exists_le_covered t
  rw [rho, dite_eq_left h]; exact (Nat.find_spec h).2

omit [Finite V] in
theorem rho_le_of_covered {t t' : ℕ} (h : Covered A t t') (ht : t ≤ t') : rho A t ≤ t' := by
  classical
  have h' : ∃ t', t ≤ t' ∧ Covered A t t' := ⟨t', ht, h⟩
  rw [rho, dite_eq_left h']; exact Nat.find_min' h' ⟨ht, h⟩

/-- Every node is activated in `[t, ϱ(t))`. -/
theorem exists_act (hA : Fair A) (v : V) (t : ℕ) : ∃ s, t ≤ s ∧ s < rho A t ∧ v ∈ A s :=
  rho_spec hA t v

theorem le_rho (hA : Fair A) (t : ℕ) : t ≤ rho A t := by
  classical
  have h := hA.exists_le_covered t
  rw [rho, dite_eq_left h]; exact (Nat.find_spec h).1

theorem lt_rho [Nonempty V] (hA : Fair A) (t : ℕ) : t < rho A t := by
  obtain ⟨s, h1, h2, -⟩ := exists_act hA (Classical.arbitrary V) t; omega

theorem rho_mono (hA : Fair A) {t t' : ℕ} (h : t ≤ t') : rho A t ≤ rho A t' :=
  rho_le_of_covered ((rho_spec hA t').mono h le_rfl) (h.trans (le_rho hA t'))

theorem rho_monotone (hA : Fair A) : Monotone (rho A) := fun _ _ h => rho_mono hA h

theorem rho_iter_mono (hA : Fair A) (n : ℕ) {t t' : ℕ} (h : t ≤ t') :
    (rho A)^[n] t ≤ (rho A)^[n] t' :=
  (rho_monotone hA).iterate n h

theorem le_rho_iter (hA : Fair A) (n : ℕ) (t : ℕ) : t ≤ (rho A)^[n] t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']; exact ih.trans (le_rho hA _)

theorem rho_iter_le_iter (hA : Fair A) {m n : ℕ} (h : m ≤ n) (t : ℕ) :
    (rho A)^[m] t ≤ (rho A)^[n] t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Function.iterate_add_apply]
  exact rho_iter_mono hA m (le_rho_iter hA d t)

omit [Finite V] in
theorem rho_iter_add (a b t : ℕ) : (rho A)^[a] ((rho A)^[b] t) = (rho A)^[a + b] t :=
  (Function.iterate_add_apply _ a b t).symm

/-- If a property `p` of times is preserved by every step that does not activate `v`, ... :
the first activation of `v` at or after `t` happens before `ϱ(t)`. -/
theorem exists_first_act (hA : Fair A) (v : V) (t : ℕ) :
    ∃ s, t ≤ s ∧ s < rho A t ∧ v ∈ A s ∧ ∀ s', t ≤ s' → s' < s → v ∉ A s' := by
  classical
  have h : ∃ s, t ≤ s ∧ v ∈ A s := hA v t
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_act hA v t
  refine ⟨Nat.find h, (Nat.find_spec h).1, ?_, (Nat.find_spec h).2, fun s' h1 h2 h3 =>
    Nat.find_min h h2 ⟨h1, h3⟩⟩
  exact lt_of_le_of_lt (Nat.find_min' h ⟨hs1, hs3⟩) hs2

end Rho

/-! ## Non-vacuity: synchronous and round-robin schedules are fair -/

/-- The synchronous schedule activates all nodes at every time. -/
def sync : ℕ → Set V := fun _ => Set.univ

theorem fair_sync : Fair (sync : ℕ → Set V) := fun _ t => ⟨t, le_rfl, Set.mem_univ _⟩

theorem rho_sync [Finite V] [Nonempty V] (t : ℕ) : rho (sync : ℕ → Set V) t = t + 1 := by
  apply le_antisymm
  · exact rho_le_of_covered (fun v => ⟨t, le_rfl, Nat.lt_succ_self t, Set.mem_univ _⟩) (by omega)
  · exact lt_rho fair_sync t

/-- A round-robin schedule: one node at a time, in the order given by `e : V ≃ Fin n`. -/
def roundRobin {n : ℕ} (e : V ≃ Fin n) : ℕ → Set V := fun t => {v | ((e v : ℕ)) = t % n}

theorem fair_roundRobin {n : ℕ} (e : V ≃ Fin n) : Fair (roundRobin e) := by
  intro v t
  have hn : 0 < n := Fin.pos (e v)
  refine ⟨t * n + n + (e v : ℕ), ?_, ?_⟩
  · nlinarith
  · simp only [roundRobin, Set.mem_ofPred_eq]
    rw [show t * n + n + (e v : ℕ) = (e v : ℕ) + n * (t + 1) by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (e v).2]

theorem rho_roundRobin_le {n : ℕ} (e : V ≃ Fin n) (t : ℕ) :
    rho (roundRobin e) t ≤ t + n := by
  refine rho_le_of_covered ?_ (by omega)
  intro v
  have hn : 0 < n := Fin.pos (e v)
  -- the next time `s ≥ t` with `s % n = e v`
  refine ⟨t + ((e v : ℕ) + n - t % n) % n, by omega, ?_, ?_⟩
  · have := Nat.mod_lt ((e v : ℕ) + n - t % n) hn; omega
  · simp only [roundRobin, Set.mem_ofPred_eq]
    have h1 := Nat.mod_lt t hn
    have h2 := (e v).2
    have e1 : (t + ((e v : ℕ) + n - t % n) % n) % n = (t % n + ((e v : ℕ) + n - t % n)) % n := by
      rw [Nat.add_mod, Nat.mod_mod]; conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
    rw [e1, show t % n + ((e v : ℕ) + n - t % n) = (e v : ℕ) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt h2]

end Cslib.StoneAge
