/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init

/-!
# Basic lemmas on lists

## Main statements

* `List.flatMap_range_eq_of_forall_ne`: a `flatMap` over `range n` of a function that is `[]`
  except at `k < n` is its value at `k`.
-/

@[expose] public section

namespace List

/-- A `flatMap` over `range n` of a function that is `[]` except at `k < n` is its value at `k`. -/
theorem flatMap_range_eq_of_forall_ne {α : Type*} {f : ℕ → List α} {k : ℕ} :
    ∀ {n : ℕ}, k < n → (∀ t, t ≠ k → f t = []) → (List.range n).flatMap f = f k := by
  intro n hk h
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_or_ge k n with h' | h'
    · rw [ih h', h n (by omega), List.append_nil]
    · obtain rfl : k = n := by omega
      rw [List.flatMap_eq_nil_iff.mpr (fun t ht => h t (by simp at ht; omega)), List.nil_append]

end List
