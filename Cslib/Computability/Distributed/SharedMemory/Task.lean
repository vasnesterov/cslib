/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Indist

/-!
# One-shot tasks in the asynchronous shared-memory model

A *task* (consensus, renaming, lattice agreement, …) is specified by a relation between the
inputs of the participating processes and the outputs of the processes that have decided. An
algorithm for a task is an `Impl` of the dummy object `taskObj In Out` (operations = inputs,
responses = outputs; its sequential specification is never used). Each process invokes the task
at most once (`OneShot`); its input is its first invocation, its output its first response.

## Main definitions

* `Task P`: input/output types and the validity relation `Δ`.
* `taskObj`, `inputs α p`, `outputs α p`, `OneShot α`.
* `Impl.Solves T`: every finite one-shot execution satisfies `T.Δ`.
* `Impl.OneShotOF`: obstruction-freedom restricted to one-shot executions (the weakest progress
  condition used by covering arguments); `WaitFree → ObstructionFree → OneShotOF`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

/-- A task for processes `P`: `Δ ins outs` says that the outputs `outs` (`some y` = decided `y`)
are allowed for the inputs `ins` (`some x` = participates with input `x`). -/
structure Task (P : Type) where
  /-- Inputs. -/
  In : Type
  /-- Outputs. -/
  Out : Type
  /-- The input/output relation (for possibly partial executions). -/
  Δ : (P → Option In) → (P → Option Out) → Prop

/-- The dummy object specification of a task: operations are inputs, responses are outputs. The
state and transition function are irrelevant (tasks are not sequential objects). -/
def taskObj (In Out : Type) [Inhabited Out] : ObjSpec where
  State := Unit
  Op := In
  Resp := Out
  init := ()
  δ _ _ := ((), default)

variable {P : Type} {A : ObjSpec}

/-- The input of `p` in the execution `α` (its first invocation). -/
def inputs [DecidableEq P] (α : List (Label P A)) (p : P) : Option A.Op := (opsOf α p).head?

/-- The output of `p` in the execution `α` (its first response). -/
def outputs [DecidableEq P] (α : List (Label P A)) (p : P) : Option A.Resp := (respsOf α p).head?

/-- Every process invokes at most one operation. -/
def OneShot [DecidableEq P] (α : List (Label P A)) : Prop := ∀ p, (opsOf α p).length ≤ 1

lemma OneShot.of_append [DecidableEq P] {α β : List (Label P A)} (h : OneShot (α ++ β)) :
    OneShot α := fun p => by
  have := h p; simp only [opsOf_append, List.length_append] at this; omega

variable {ι : Type} {B : ι → ObjSpec} {L : Type} [DecidableEq P] [DecidableEq ι]

namespace Impl

variable {In Out : Type} [Inhabited Out]

/-- The algorithm `I` solves the task `T` (safety): in every finite one-shot execution, the
inputs and outputs satisfy `T.Δ`. -/
def Solves (T : Task P) [Inhabited T.Out] (I : Impl (taskObj T.In T.Out) B P L) : Prop :=
  ∀ α, I.Valid α → OneShot α → T.Δ (inputs α) (outputs α)

variable (I : Impl A B P L)

/-- Obstruction-freedom for one-shot executions: from every configuration reached by a one-shot
execution, a pending process running solo returns. -/
def OneShotOF : Prop :=
  ∀ α C p, I.run α = some C → OneShot α → C.pend p ≠ none →
    ∃ k, ((I.soloStep p)^[k] C).pend p = none

lemma ObstructionFree.oneShotOF (h : I.ObstructionFree) : I.OneShotOF :=
  fun α C p hα _ hp => h C p ⟨α, hα⟩ hp

lemma WaitFree.oneShotOF (h : I.WaitFree) : I.OneShotOF :=
  (WaitFree.obstructionFree I h).oneShotOF I

/-- A process that never invokes anything takes no step at all. -/
lemma proc_ne_of_opsOf_eq_nil {α : List (Label P A)} {C : Config A B P L} (h : I.run α = some C)
    {z : P} (hz : opsOf α z = []) : ∀ ℓ ∈ α, ℓ.proc ≠ z := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simp
  | append_singleton β ℓ ih =>
    rw [run, runFrom_append] at h
    cases hβ : I.runFrom I.initCfg β with
    | none => simp [hβ] at h
    | some C₁ =>
      simp only [hβ, Option.bind_some, runFrom_singleton] at h
      have hzβ : opsOf β z = [] := by
        simp only [opsOf_append, List.append_eq_nil_iff] at hz; exact hz.1
      have hpend : C₁.pend z = none := by
        rcases I.run_counts hβ z with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact h1
        · rw [hzβ] at h2; simp at h2
      intro ℓ' hℓ'
      rcases List.mem_append.1 hℓ' with hℓ' | hℓ'
      · exact ih hβ hzβ ℓ' hℓ'
      · simp only [List.mem_singleton] at hℓ'; subst hℓ'
        intro hp
        cases ℓ' with
        | inv q o =>
          simp only [Label.proc] at hp; subst hp
          simp [opsOf_append] at hz
        | tau q =>
          simp only [Label.proc] at hp; subst hp
          exact (step_tau h).1 hpend
        | ret q r =>
          simp only [Label.proc] at hp; subst hp
          exact (step_ret h).1 hpend

end Impl

end Cslib.SharedMemory
