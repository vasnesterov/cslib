/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Spec

/-!
# Atomic snapshot objects

`snapObj n` is the `n`-component atomic snapshot over `ℕ`: `update i v` writes `v` into
component `i` (returning the zero view), `scan` returns all components atomically. The
single-writer discipline ("process `i` updates component `i`") is imposed by the
implementation's `allowed` predicate, since objects cannot see the caller.
-/

@[expose] public section

namespace Cslib.SharedMemory

/-- Operations of an `n`-component snapshot over `ℕ`. -/
inductive SnapOp (n : ℕ) where
  | update (i : Fin n) (v : ℕ)
  | scan
  deriving DecidableEq

/-- `n`-component atomic snapshot over `ℕ` (all components initially `0`); `update` returns the
zero view as acknowledgement. -/
abbrev snapObj (n : ℕ) : ObjSpec where
  State := Fin n → ℕ
  Op := SnapOp n
  Resp := Fin n → ℕ
  init := fun _ => 0
  δ q
    | .update i v => (Function.update q i v, fun _ => 0)
    | .scan => (q, q)

@[simp] lemma snapObj_update (n : ℕ) (q : Fin n → ℕ) (i : Fin n) (v : ℕ) :
    (snapObj n).δ q (.update i v) = (Function.update q i v, fun _ => 0) := rfl

@[simp] lemma snapObj_scan (n : ℕ) (q : Fin n → ℕ) : (snapObj n).δ q .scan = (q, q) := rfl

end Cslib.SharedMemory
