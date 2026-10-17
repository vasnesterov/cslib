/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Seq

/-!
# Deterministic sequential specifications

`detSpec init δ` is the set of complete sequential histories of a deterministic object with
initial state `init` and transition function `δ`.

## Main results

* `seqHist_mem_detSpec`: membership in `detSpec` is `runOK`.
* `detSpec_total`: all operations of a deterministic object are total.
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

variable {P X Op Res State : Type}

/-- The state reached by running the operations of `M`. -/
def runState (δ : State → Op → State × Res) (q : State) (M : List (OpRec P X Op Res)) : State :=
  M.foldl (fun q e => (δ q e.o).1) q

@[simp] lemma runOK_nil (δ : State → Op → State × Res) (q : State) :
    runOK δ q ([] : List (OpRec P X Op Res)) := trivial

@[simp] lemma runOK_cons (δ : State → Op → State × Res) (q : State) (e : OpRec P X Op Res)
    (M : List (OpRec P X Op Res)) :
    runOK δ q (e :: M) ↔ (δ q e.o).2 = e.r ∧ runOK δ (δ q e.o).1 M := Iff.rfl

lemma runOK_append (δ : State → Op → State × Res) (q : State) (M N : List (OpRec P X Op Res)) :
    runOK δ q (M ++ N) ↔ runOK δ q M ∧ runOK δ (runState δ q M) N := by
  induction M generalizing q with
  | nil => simp [runState]
  | cons e M ih => simp [ih, runState, and_assoc]

lemma seqHist_mem_detSpec {init : State} {δ : State → Op → State × Res}
    {M : List (OpRec P X Op Res)} : seqHist M ∈ detSpec init δ ↔ runOK δ init M := by
  constructor
  · rintro ⟨M', h, h'⟩; rwa [seqHist_injective h]
  · intro h; exact ⟨M, rfl, h⟩

/-- Every operation of a deterministic object is total. -/
lemma detSpec_total (init : State) (δ : State → Op → State × Res) (p : P) (x : X) (o : Op) :
    Total (fun _ : X => detSpec init δ) p x o := by
  intro M _ hM
  rw [seqHist_mem_detSpec] at hM
  refine ⟨(δ (runState δ init M) o).2, ?_⟩
  rw [seqHist_mem_detSpec, runOK_append]
  exact ⟨hM, by simp⟩

end Cslib.SharedMemory.HerlihyWing
