/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Spec
public import Mathlib.Order.Basic

/-!
# Max registers

A *max register* stores the maximum of the values written so far.
`maxRegObj` is the max register over `ℕ` (`writeMax v` sets the value to `max q v` and returns
`0`; `readMax` returns the value).
-/

@[expose] public section

namespace Cslib.SharedMemory

/-- Operations of the max register `maxRegObj` over `ℕ`. -/
inductive MaxOp where
  | writeMax (v : ℕ)
  | readMax
  deriving DecidableEq

/-- Max register over `ℕ` (initially `0`); `writeMax` returns `0` as acknowledgement. -/
abbrev maxRegObj : ObjSpec where
  State := ℕ
  Op := MaxOp
  Resp := ℕ
  init := 0
  δ q
    | .writeMax v => (max q v, 0)
    | .readMax => (q, q)

@[simp] lemma maxRegObj_writeMax (q v : ℕ) : maxRegObj.δ q (.writeMax v) = (max q v, 0) := rfl

@[simp] lemma maxRegObj_readMax (q : ℕ) : maxRegObj.δ q .readMax = (q, q) := rfl

end Cslib.SharedMemory
