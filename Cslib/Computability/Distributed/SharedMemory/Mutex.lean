/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Progress

/-!
# Mutual exclusion (lock objects) in the asynchronous shared-memory model

A *lock* (mutex) is implemented as an `Impl mutexObj B P L`: the high-level operations are
`lock` and `unlock` (both with a trivial response). The *client* uses them in the pattern
`lock(); critical section; unlock()`; the state of a process with respect to this pattern (its
*region*) is computed from the history (`regionOf`):

* `rem` (remainder section) —`inv lock`→ `trying` —`ret`→ `cs` (critical section)
  —`inv unlock`→ `exiting` —`ret`→ `rem`.

An execution is *client-well-formed* (`ClientWF`) if every process follows this pattern.

* `MutualExclusion I`: in every finite client-well-formed execution at most one process is in
  its critical section.
* `InfExec.Fair e`: every process with a pending operation eventually takes a step (so it either
  finishes its operation or takes infinitely many steps).
* `DeadlockFree I`: in every fair client-well-formed infinite execution, if at some time some
  process has a pending `lock`/`unlock` and no process is in the critical section, then some
  `lock`/`unlock` operation completes later.

These are the definitions used e.g. by Aghazadeh–Imbs–Raynal–Taubenfeld–Woelfel (PODC 2019),
§2.3: deadlock-freedom does not require processes to leave the critical section.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

/-- Operations of a lock object. -/
inductive MutexOp
  | lock
  | unlock
  deriving DecidableEq

/-- The (dummy) object specification of a lock: operations `lock`/`unlock`, trivial responses.
Its sequential specification is never used. -/
abbrev mutexObj : ObjSpec where
  State := Unit
  Op := MutexOp
  Resp := Unit
  init := ()
  δ _ _ := ((), ())

/-- The region of a process with respect to the pattern `lock(); CS; unlock()`. -/
inductive Region
  | rem
  | trying
  | cs
  | exiting
  deriving DecidableEq

namespace Region

/-- Effect of a label of the process on its region (`none`: the pattern is violated). -/
def next {P : Type} : Region → Label P mutexObj → Option Region
  | rem, .inv _ .lock => some trying
  | trying, .ret _ _ => some cs
  | cs, .inv _ .unlock => some exiting
  | exiting, .ret _ _ => some rem
  | r, .tau _ => some r
  | _, _ => none

end Region

variable {P : Type} [DecidableEq P]

/-- Region of `p` after the execution `α` (`none` if `p` violated the client pattern). -/
def regionOf (α : List (Label P mutexObj)) (p : P) : Option Region :=
  α.foldl (fun r ℓ => if ℓ.proc = p then r.bind (fun r => r.next ℓ) else r) (some .rem)

@[simp] lemma regionOf_nil (p : P) : regionOf ([] : List (Label P mutexObj)) p = some .rem := rfl

lemma regionOf_append_singleton (α : List (Label P mutexObj)) (ℓ : Label P mutexObj) (p : P) :
    regionOf (α ++ [ℓ]) p =
      if ℓ.proc = p then (regionOf α p).bind (fun r => r.next ℓ) else regionOf α p := by
  simp [regionOf, List.foldl_append]

lemma regionOf_append_singleton_of_ne (α : List (Label P mutexObj)) (ℓ : Label P mutexObj)
    {p : P} (h : ℓ.proc ≠ p) : regionOf (α ++ [ℓ]) p = regionOf α p := by
  simp [regionOf_append_singleton, h]

/-- Every process follows the client pattern `lock(); CS; unlock()` in `α`. -/
def ClientWF (α : List (Label P mutexObj)) : Prop := ∀ p, regionOf α p ≠ none

/-- `p` is in its critical section after `α`. -/
def InCS (α : List (Label P mutexObj)) (p : P) : Prop := regionOf α p = some .cs

variable {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}

namespace Impl

variable (I : Impl mutexObj B P L)

/-- **Mutual exclusion**: in every finite client-well-formed execution, at most one process is
in its critical section. -/
def MutualExclusion : Prop :=
  ∀ α, I.Valid α → ClientWF α → ∀ p q, InCS α p → InCS α q → p = q

/-- The labels of the first `t` steps of an infinite execution. -/
def InfExec.pre {I : Impl mutexObj B P L} (e : I.InfExec) (t : ℕ) : List (Label P mutexObj) :=
  (List.range t).map e.lbl

/-- An infinite execution is *fair* if every process with a pending operation eventually takes a
step (internal step or response). Iterating, a process with a pending operation either completes
it or takes infinitely many steps. -/
def InfExec.Fair {I : Impl mutexObj B P L} (e : I.InfExec) : Prop :=
  ∀ p t, (e.cfg t).pend p ≠ none → ∃ t' ≥ t, (e.lbl t').proc = p ∧ (e.lbl t').IsStep

/-- **Deadlock-freedom**: in every fair client-well-formed infinite execution, if at time `t` some
process has a pending `lock()`/`unlock()` and no process is in its critical section, then some
`lock()`/`unlock()` operation completes at some time `t' ≥ t`. -/
def DeadlockFree : Prop :=
  ∀ e : I.InfExec, (∀ t, ClientWF (e.pre t)) → e.Fair → ∀ t,
    (∃ p, (e.cfg t).pend p ≠ none) → (∀ q, ¬ InCS (e.pre t) q) →
      ∃ t' ≥ t, ∃ p r, e.lbl t' = .ret p r

variable {I}

lemma InfExec.pre_succ (e : I.InfExec) (t : ℕ) : e.pre (t + 1) = e.pre t ++ [e.lbl t] := by
  simp [InfExec.pre, List.range_succ]

lemma InfExec.run_pre (e : I.InfExec) (t : ℕ) : I.run (e.pre t) = some (e.cfg t) := by
  induction t with
  | zero => simp [InfExec.pre, e.cfg_zero]
  | succ t ih =>
    rw [e.pre_succ, I.run_append_of_eq ih, I.runFrom_singleton, e.step_eq]

lemma InfExec.valid_pre (e : I.InfExec) (t : ℕ) : I.Valid (e.pre t) := ⟨_, e.run_pre t⟩

/-- **Progress by a measure.** Let `Good` be a property of times and `μ` a measure. Suppose that
from time `t` on, as long as `Good` fails, process `p` eventually takes a step, each step of `p`
makes `Good` true or decreases `μ`, and other labels make `Good` true or do not increase `μ`.
Then `Good` eventually holds. -/
lemma InfExec.exists_good (e : I.InfExec) (p : P) (Good : ℕ → Prop) (μ : ℕ → ℕ) (t : ℕ)
    (hstep : ∀ t' ≥ t, ¬ Good t' → ∃ t'' ≥ t', (e.lbl t'').proc = p ∧ (e.lbl t'').IsStep)
    (hp : ∀ t' ≥ t, ¬ Good t' → (e.lbl t').proc = p → (e.lbl t').IsStep →
      Good (t' + 1) ∨ μ (t' + 1) < μ t')
    (ho : ∀ t' ≥ t, ¬ Good t' → ¬ ((e.lbl t').proc = p ∧ (e.lbl t').IsStep) →
      Good (t' + 1) ∨ μ (t' + 1) ≤ μ t') :
    ∃ t' ≥ t, Good t' := by
  induction hn : μ t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    by_contra hcon
    push Not at hcon
    obtain ⟨t'', ht'', hpt, hst⟩ := hstep t le_rfl (hcon t le_rfl)
    -- between `t` and `t''` the measure does not increase
    have hle : ∀ k, t + k ≤ t'' → μ (t + k) ≤ n := by
      intro k
      induction k with
      | zero => intro _; simp [hn]
      | succ k ihk =>
        intro hk
        have h1 := ihk (by omega)
        by_cases hpk : (e.lbl (t + k)).proc = p ∧ (e.lbl (t + k)).IsStep
        · rcases hp (t + k) (by omega) (hcon _ (by omega)) hpk.1 hpk.2 with h | h
          · exact absurd h (hcon _ (by omega))
          · rw [← Nat.add_assoc]; omega
        · rcases ho (t + k) (by omega) (hcon _ (by omega)) hpk with h | h
          · exact absurd h (hcon _ (by omega))
          · rw [← Nat.add_assoc]; omega
    have h2 := hle (t'' - t) (by omega)
    rw [show t + (t'' - t) = t'' by omega] at h2
    rcases hp t'' ht'' (hcon _ ht'') hpt hst with h | h
    · exact hcon _ (by omega) h
    · obtain ⟨t₃, ht₃, hg⟩ := ih (μ (t'' + 1)) (by omega) (t'' + 1)
        (fun t' ht' hg => hstep t' (by omega) hg)
        (fun t' ht' hg => hp t' (by omega) hg)
        (fun t' ht' hg => ho t' (by omega) hg) rfl
      exact hcon t₃ (by omega) hg

end Impl

end Cslib.SharedMemory
