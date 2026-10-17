/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Spec
public import Mathlib.Algebra.Group.Defs

/-!
# Fetch&add and fetch&increment objects

Sequential specifications (`ObjSpec`) of the fetch&add family. Every operation returns the old
value.

* `faaObj V` — fetch&add over an additive monoid `V` (initially `0`; the only operation is
  `faa a`, given by its argument `a : V`);
* `rfaiObj` — readable fetch&increment over `ℕ` (`fai` / `read`, initially `0`);
* `modFaiObj m` — readable fetch&increment modulo `m` over `ℕ` (`fai` sets the value to
  `(v + 1) % m`).
-/

@[expose] public section

namespace Cslib.SharedMemory

/-- Fetch&add over `V`: `δ q a = (q + a, q)`. -/
abbrev faaObj (V : Type) [AddMonoid V] : ObjSpec where
  State := V
  Op := V
  Resp := V
  init := 0
  δ q a := (q + a, q)

@[simp] lemma faaObj_δ (V : Type) [AddMonoid V] (q a : V) : (faaObj V).δ q a = (q + a, q) := rfl

/-- Operations of a readable fetch&increment. -/
inductive FAIOp where
  | fai
  | read
  deriving DecidableEq

/-- Readable fetch&increment over `ℕ` (initially `0`). -/
abbrev rfaiObj : ObjSpec where
  State := ℕ
  Op := FAIOp
  Resp := ℕ
  init := 0
  δ q
    | .fai => (q + 1, q)
    | .read => (q, q)

@[simp] lemma rfaiObj_fai (q : ℕ) : rfaiObj.δ q .fai = (q + 1, q) := rfl

@[simp] lemma rfaiObj_read (q : ℕ) : rfaiObj.δ q .read = (q, q) := rfl

/-- Readable fetch&increment modulo `m` over `ℕ` (initially `0`; the reachable values are
`0, …, m - 1` when `m > 0`). -/
abbrev modFaiObj (m : ℕ) : ObjSpec where
  State := ℕ
  Op := FAIOp
  Resp := ℕ
  init := 0
  δ q
    | .fai => ((q + 1) % m, q)
    | .read => (q, q)

@[simp] lemma modFaiObj_fai (m q : ℕ) : (modFaiObj m).δ q .fai = ((q + 1) % m, q) := rfl

@[simp] lemma modFaiObj_read (m q : ℕ) : (modFaiObj m).δ q .read = (q, q) := rfl

end Cslib.SharedMemory
