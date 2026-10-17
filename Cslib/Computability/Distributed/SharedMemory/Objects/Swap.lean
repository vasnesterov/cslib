/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Spec

/-!
# Swap objects

* `swapObj D d₀` — a swap object with values `D` (initially `d₀`): the only operation,
  `swap(v)` (given by its argument `v : D`), sets the value to `v` and returns the old value;
* `rswapObj D d₀` — a readable swap object (`read` / `swap v`).
-/

@[expose] public section

namespace Cslib.SharedMemory

/-- A swap object with values `D`: `swap(v)` sets the value to `v` and returns the old value. -/
abbrev swapObj (D : Type) (d₀ : D) : ObjSpec where
  State := D
  Op := D
  Resp := D
  init := d₀
  δ s v := (v, s)

@[simp] lemma swapObj_δ (D : Type) (d₀ s v : D) : (swapObj D d₀).δ s v = (v, s) := rfl

/-- Operations of a readable swap object. -/
inductive RSOp (D : Type) where
  /-- `read()`. -/
  | read
  /-- `swap(v)`. -/
  | swap (v : D)
  deriving DecidableEq

/-- A readable swap object with values `D`. -/
abbrev rswapObj (D : Type) (d₀ : D) : ObjSpec where
  State := D
  Op := RSOp D
  Resp := D
  init := d₀
  δ s
    | .read => (s, s)
    | .swap v => (v, s)

@[simp] lemma rswapObj_read (D : Type) (d₀ s : D) : (rswapObj D d₀).δ s .read = (s, s) := rfl

@[simp] lemma rswapObj_swap (D : Type) (d₀ s v : D) :
    (rswapObj D d₀).δ s (.swap v) = (v, s) := rfl

end Cslib.SharedMemory
