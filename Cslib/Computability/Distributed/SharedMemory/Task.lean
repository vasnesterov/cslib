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
  condition used by covering arguments); `WaitFree → ObstructionFree → OneShotOF`. It is
  `ObstructionFreeOn OneShot` (`Impl.oneShotOF_iff`); one-shot executions are closed under
  prefixes (`prefixClosed_oneShot`).

## Inputs and outputs under extensions

* `outputs_append`, `outputs_concat`, `outputs_concat_of_ne`, `outputs_append_of_ne_none`,
  `outputs_append_ne_none`, `outputs_append_inv`, `outputs_append_tau`: the output of a process
  (its first response) after extending the execution; `outputs_ne_none_of_mem`,
  `outputs_eq_none_of_proc_ne`.
* `inputs_append_of_ne_none`: an input, once given, does not change.
* `OneShot.append_inv`, `OneShot.append_of_opsOf_nil`: extending one-shot executions.
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

lemma prefixClosed_oneShot [DecidableEq P] : PrefixClosed (OneShot (P := P) (A := A)) :=
  fun _ _ h => h.of_append

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

/-- One-shot obstruction-freedom is obstruction-freedom on one-shot executions. -/
lemma oneShotOF_iff : I.OneShotOF ↔ I.ObstructionFreeOn OneShot := Iff.rfl

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

/-! ## Inputs and outputs under extensions -/

namespace Cslib.SharedMemory

variable {P : Type} [DecidableEq P] {A : ObjSpec}

/-! ### Outputs -/

/-- The output after a concatenation: the output before it, or the first output in the
extension. -/
lemma outputs_append (α β : List (Label P A)) (p : P) :
    outputs (α ++ β) p = (outputs α p).or (outputs β p) := by
  simp [outputs, respsOf_append, List.head?_append]

/-- The output after appending one label. -/
lemma outputs_concat (α : List (Label P A)) (ℓ : Label P A) (p : P) :
    outputs (α ++ [ℓ]) p = (outputs α p).or (ℓ.retOf p) := by
  rw [outputs_append]; congr 1; cases h : ℓ.retOf p <;> simp [outputs, h]

/-- Appending a label that is not a response of `p` does not change the output of `p`. -/
lemma outputs_concat_of_ne {α : List (Label P A)} {ℓ : Label P A} {p : P}
    (h : ∀ r, ℓ ≠ .ret p r) : outputs (α ++ [ℓ]) p = outputs α p := by
  simp only [outputs, respsOf_concat_of_ne h]

/-- An output, once given, does not change. -/
lemma outputs_append_of_ne_none {α : List (Label P A)} (β : List (Label P A)) {p : P}
    (h : outputs α p ≠ none) : outputs (α ++ β) p = outputs α p := by
  rw [outputs_append]
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 h
  simp [hr]

/-- A process that has output keeps its output. -/
lemma outputs_append_ne_none {α : List (Label P A)} (β : List (Label P A)) {p : P}
    (h : outputs α p ≠ none) : outputs (α ++ β) p ≠ none := by
  rwa [outputs_append_of_ne_none β h]

/-- Invocations do not change outputs. -/
@[simp] lemma outputs_append_inv (α : List (Label P A)) (p q : P) (o : A.Op) :
    outputs (α ++ [.inv p o]) q = outputs α q := outputs_concat_of_ne (by simp)

/-- Internal steps do not change outputs. -/
@[simp] lemma outputs_append_tau (α : List (Label P A)) (p q : P) :
    outputs (α ++ [.tau p]) q = outputs α q := outputs_concat_of_ne (by simp)

/-- A process that has returned has an output. -/
lemma outputs_ne_none_of_mem {α : List (Label P A)} {p : P} {r : A.Resp}
    (h : Label.ret p r ∈ α) : outputs α p ≠ none := by
  unfold outputs respsOf
  intro hn
  rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at hn
  simpa using hn _ h

/-- A process without labels in the execution has no output. -/
lemma outputs_eq_none_of_proc_ne {α : List (Label P A)} {p : P} (h : ∀ ℓ ∈ α, ℓ.proc ≠ p) :
    outputs α p = none := by
  simp [outputs, respsOf_eq_nil_of_proc_ne h]

/-! ### Inputs -/

/-- An input, once given, does not change. -/
lemma inputs_append_of_ne_none {α : List (Label P A)} (β : List (Label P A)) {p : P}
    (h : inputs α p ≠ none) : inputs (α ++ β) p = inputs α p := by
  simp only [inputs, opsOf_append] at h ⊢
  rw [List.head?_append]
  cases hh : (opsOf α p).head? with
  | none => exact absurd hh h
  | some x => rfl

/-! ### One-shot executions -/

/-- A process that has not invoked anything may invoke an operation in a one-shot execution. -/
lemma OneShot.append_inv {α : List (Label P A)} (h : OneShot α) {p : P} (hp : opsOf α p = [])
    (o : A.Op) : OneShot (α ++ [.inv p o]) := by
  intro q
  by_cases hq : q = p
  · subst hq; simp [opsOf_append, hp]
  · have := h q
    simp only [opsOf_append, opsOf_cons, opsOf_nil, List.length_append]
    rw [Label.invOf_eq_none_of_proc_ne (by simpa [Label.proc] using Ne.symm hq)]
    simpa using this

/-- Appending labels without invocations keeps an execution one-shot. -/
lemma OneShot.append_of_opsOf_nil {α β : List (Label P A)} (h : OneShot α)
    (hβ : ∀ p, opsOf β p = []) : OneShot (α ++ β) := by
  intro p; simpa [opsOf_append, hβ p] using h p

end Cslib.SharedMemory
