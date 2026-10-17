/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Logic.Function.Iterate

/-!
# Time-dependent iteration

Synchronous distributed algorithms, adversaries and random processes are usually run by a
*time-dependent* step function: the state after `t + 1` rounds is `f t` applied to the state after
`t` rounds. `Nat.timeRec f a t` is this run (`Function.iterate` is the time-independent special
case, `Nat.timeRec_const`). The lemmas below are the facts that every run of a synchronous model
re-proves: splitting a run at an intermediate time (`timeRec_add`, `timeRec_succ'`), simulation of
one run by another along a map (`timeRec_semiconj`), and stable states (`Nat.eq_of_le_of_stable`:
once a run reaches a state in which the step does nothing, e.g. a node's final output, it stays
there).

## Main definitions

* `Nat.timeRec f a t`: `f (t - 1) (⋯ (f 1 (f 0 a)))`.

## Main statements

* `Nat.timeRec_add`: running for `s + t` steps is running for `s` steps and then, from the
  resulting state, for `t` steps with the step functions shifted by `s`.
* `Nat.timeRec_succ'`: the first step, then the run shifted by one.
* `Nat.timeRec_semiconj`: a map `e` with `e ∘ f t = g t ∘ e` maps runs of `f` to runs of `g`.
* `Nat.timeRec_const`: time-independent runs are iterates.
* `Nat.eq_of_le_of_stable`: a sequence that does not move while `P` holds is constant once `P`
  holds.
-/

@[expose] public section

namespace Nat

variable {α β : Type*}

/-- The run of the time-dependent step functions `f t` from `a`:
`timeRec f a 0 = a` and `timeRec f a (t + 1) = f t (timeRec f a t)`. -/
def timeRec (f : ℕ → α → α) (a : α) : ℕ → α
  | 0 => a
  | t + 1 => f t (timeRec f a t)

variable (f : ℕ → α → α) (a : α)

/-- A run of length `0` stays at the initial state. -/
@[simp] theorem timeRec_zero : timeRec f a 0 = a := rfl

/-- The step equation of `timeRec`. -/
@[simp] theorem timeRec_succ (t : ℕ) : timeRec f a (t + 1) = f t (timeRec f a t) := rfl

/-- Running for `s + t` steps is running for `s` steps and then for `t` steps with the step
functions shifted by `s`. -/
theorem timeRec_add (s t : ℕ) :
    timeRec f a (s + t) = timeRec (fun k => f (s + k)) (timeRec f a s) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [← Nat.add_assoc, timeRec_succ, timeRec_succ, ih]

/-- A run is its first step followed by the run of the shifted step functions. -/
theorem timeRec_succ' (t : ℕ) :
    timeRec f a (t + 1) = timeRec (fun k => f (k + 1)) (f 0 a) t := by
  rw [Nat.add_comm, timeRec_add]
  simp only [Nat.add_comm 1]
  rfl

/-- A map that intertwines the step functions maps runs to runs. -/
theorem timeRec_semiconj {g : ℕ → β → β} {e : α → β} (h : ∀ t x, e (f t x) = g t (e x))
    (t : ℕ) : e (timeRec f a t) = timeRec g (e a) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [timeRec_succ, timeRec_succ, h, ih]

/-- Time-independent runs are iterates. -/
@[simp] theorem timeRec_const (g : α → α) (t : ℕ) : timeRec (fun _ => g) a t = g^[t] a := by
  induction t with
  | zero => rfl
  | succ t ih => rw [timeRec_succ, ih, Function.iterate_succ_apply']

/-- **Stable states.** If the sequence `x` does not move at time `t` whenever `P (x t)` holds,
then once `P (x s)` holds the sequence is constant from `s` on. -/
theorem eq_of_le_of_stable {x : ℕ → α} {P : α → Prop} (h : ∀ t, P (x t) → x (t + 1) = x t)
    {s t : ℕ} (hs : P (x s)) (hst : s ≤ t) : x t = x s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  clear hst
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, h _ (ih ▸ hs), ih]

end Nat
