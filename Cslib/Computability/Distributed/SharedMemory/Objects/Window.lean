/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Spec

/-!
# Window registers

The `w`-window register of Mostéfaoui, Perrin and Raynal (`windowObj V w`) stores the sequence
of the last `w` values written (fewer if fewer were written); `read` returns the sequence. A
`1`-window register is a standard register; the consensus number of a `w`-window register is
`w`.

## Main statements

* `windowObj_runOps_writes`: after at least one write, the window consists of the last `w`
  values of the full history of writes.
-/

@[expose] public section

/-- The last `n` elements of `s ++ l` are those of `l` if `l` has at least `n` elements. -/
lemma List.drop_length_sub_append_eq {α : Type*} (s : List α) {l : List α} {n : ℕ}
    (h : n ≤ l.length) : (s ++ l).drop ((s ++ l).length - n) = l.drop (l.length - n) := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by simp; omega)]
  simp only [List.length_append, List.nil_append]
  congr 1; omega

namespace Cslib.SharedMemory

/-- Operations of a window register. -/
inductive WinOp (V : Type) where
  /-- Append a value. -/
  | write (v : V)
  /-- Read the window. -/
  | read
  deriving DecidableEq

/-- The `w`-window register over `V`, initially empty (`⊥`): the state is the list of the last
(at most) `w` values written, oldest first. -/
abbrev windowObj (V : Type) (w : ℕ) : ObjSpec where
  State := List V
  Op := WinOp V
  Resp := List V
  init := []
  δ s
    | .write v => ((s ++ [v]).drop (s.length + 1 - w), [])
    | .read => (s, s)

section windowObj

variable {V : Type} {w : ℕ}

@[simp] lemma windowObj_write (s : List V) (v : V) :
    (windowObj V w).δ s (.write v) = ((s ++ [v]).drop (s.length + 1 - w), []) := rfl

@[simp] lemma windowObj_read (s : List V) : (windowObj V w).δ s .read = (s, s) := rfl

/-- The window after a write, in terms of the full history `t` (the state is its last `w`
values). -/
lemma windowObj_write_last (t : List V) (v : V) :
    ((windowObj V w).δ (t.drop (t.length - w)) (.write v)).1 =
      (t ++ [v]).drop ((t ++ [v]).length - w) := by
  simp only [List.drop_append, List.drop_drop, List.length_drop,
    List.length_append, List.length_singleton]
  congr 2 <;> omega

/-- Writes `vs` starting from the window of the history `t`: the result is the window of
`t ++ vs`. -/
lemma windowObj_runOps_writes_last (t : List V) (vs : List V) :
    (windowObj V w).runOps (t.drop (t.length - w)) (vs.map WinOp.write) =
      (t ++ vs).drop ((t ++ vs).length - w) := by
  induction vs generalizing t with
  | nil => simp [ObjSpec.runOps]
  | cons v vs ih =>
    rw [List.map_cons, ObjSpec.runOps_cons, windowObj_write_last, ih]
    simp

/-- After at least one write, the window is the last `w` values of the full history. -/
lemma windowObj_runOps_writes (s : List V) (v : V) (vs : List V) :
    (windowObj V w).runOps s ((v :: vs).map WinOp.write) =
      (s ++ v :: vs).drop ((s ++ v :: vs).length - w) := by
  rw [List.map_cons, ObjSpec.runOps_cons]
  have : ((windowObj V w).δ s (.write v)).1 = (s ++ [v]).drop ((s ++ [v]).length - w) := by
    simp only [List.length_append, List.length_singleton]
  rw [this, windowObj_runOps_writes_last]
  simp

end windowObj

end Cslib.SharedMemory
