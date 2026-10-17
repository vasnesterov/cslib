/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.PopulationProtocols.Basic

/-! # Executions from schedules

Every schedule of pairs of distinct agents determines a unique execution from a given initial
configuration (`Execution.ofSched`). A schedule that, after a finite prefix, cycles through a list
containing all ordered pairs of distinct agents is weakly fair (`Execution.weaklyFair_of_cycle`).
This is useful to build concrete (counter)example executions.
-/

@[expose] public section

namespace Cslib.PopulationProtocol

namespace Protocol

variable {Q A : Type*} [DecidableEq A] (P : Protocol Q)

/-- The configurations visited when following schedule `σ` from `C0`. -/
def runSched (C0 : Config A Q) (σ : ℕ → A × A) : ℕ → Config A Q
  | 0 => C0
  | t + 1 => P.interact (runSched C0 σ t) (σ t).1 (σ t).2

/-- The execution determined by a schedule of distinct pairs. -/
def Execution.ofSched (C0 : Config A Q) (σ : ℕ → A × A) (hσ : ∀ t, (σ t).1 ≠ (σ t).2) :
    P.Execution A where
  config := P.runSched C0 σ
  sched := σ
  sched_ne := hσ
  step _ := rfl

@[simp] lemma Execution.ofSched_config_zero (C0 : Config A Q) (σ : ℕ → A × A)
    (hσ : ∀ t, (σ t).1 ≠ (σ t).2) : (Execution.ofSched P C0 σ hσ).config 0 = C0 := rfl

/-- A schedule which from time `m` on cycles through a list `L` that contains every ordered pair
of distinct agents is weakly fair. -/
lemma Execution.weaklyFair_of_cycle {E : P.Execution A} (L : List (A × A)) (hL : L ≠ [])
    (m : ℕ)
    (hsched : ∀ t, E.sched (m + t) = L[t % L.length]'(Nat.mod_lt _ (List.length_pos_iff.2 hL)))
    (hall : ∀ a b, a ≠ b → (a, b) ∈ L) : E.WeaklyFair := by
  intro a b hab T
  obtain ⟨i, hi, hiL⟩ := List.getElem_of_mem (hall a b hab)
  have h1 : 1 ≤ L.length := List.length_pos_iff.2 hL
  have h2 : T ≤ T * L.length := Nat.le_mul_of_pos_right T h1
  refine ⟨m + (T * L.length + i), by omega, Or.inl ?_⟩
  rw [hsched]
  have : (T * L.length + i) % L.length = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  simp only [this, hiL]

end Protocol

end Cslib.PopulationProtocol
