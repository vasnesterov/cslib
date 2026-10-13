/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Task

/-!
# The consensus task

Consensus as a one-shot task (see `Cslib.Computability.Distributed.SharedMemory.Task`): every
process invokes the task with its input and returns its decision.

* `consensus P V`: **agreement** (all decisions are equal) and **validity** (every decision is the
  input of a participating process). This is the standard specification.
* `weakConsensus P V`: agreement and **weak validity** (if all participating processes have the same
  input `v`, then every decision is `v`). Every algorithm solving `consensus` solves
  `weakConsensus` (`Impl.Solves.weakConsensus`), so lower bounds proved for `weakConsensus` are
  stronger. Weak validity is also implied by the validity condition of the "every process has an
  input from the start" formulation used by many papers (e.g. Ellen–Gelashvili–Shavit–Zhu, PODC'16:
  "equal to the input of one of the processes", where processes that never take a step still have
  an input).

An algorithm for consensus on values `V` is an `Impl (taskObj V V) B P L`.
-/

@[expose] public section

namespace Cslib.SharedMemory

/-- The consensus task on values `V`: agreement and (strong) validity. -/
def consensus (P V : Type) : Task P where
  In := V
  Out := V
  Δ ins outs := (∀ p q x y, outs p = some x → outs q = some y → x = y) ∧
    ∀ p y, outs p = some y → ∃ q, ins q = some y

/-- Consensus with *weak validity*: agreement, and if all participants have input `v` then every
decision is `v`. -/
def weakConsensus (P V : Type) : Task P where
  In := V
  Out := V
  Δ ins outs := (∀ p q x y, outs p = some x → outs q = some y → x = y) ∧
    ∀ v, (∀ q x, ins q = some x → x = v) → ∀ p y, outs p = some y → y = v

instance {P V : Type} [Inhabited V] : Inhabited (consensus P V).Out := inferInstanceAs (Inhabited V)

instance {P V : Type} [Inhabited V] : Inhabited (weakConsensus P V).Out :=
  inferInstanceAs (Inhabited V)

variable {P V : Type} [Inhabited V] [DecidableEq P] {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
  {L : Type}

/-- Validity implies weak validity. -/
theorem Impl.Solves.weakConsensus {I : Impl (taskObj V V) B P L}
    (h : I.Solves (consensus P V)) : I.Solves (weakConsensus P V) := by
  intro α hα h1
  obtain ⟨hag, hval⟩ := h α hα h1
  refine ⟨hag, fun v hv p y hy => ?_⟩
  obtain ⟨q, hq⟩ := hval p y hy
  exact hv q y hq

end Cslib.SharedMemory
