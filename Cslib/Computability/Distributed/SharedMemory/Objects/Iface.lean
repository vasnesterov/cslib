/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Task

/-!
# Interface-only objects

Some objects are not specified sequentially: tasks (consensus, renaming, election, …),
timestamp objects or nondeterministic objects are specified by properties of executions. To use
the `Impl` framework for them, one only needs their operation and response types; the state and
the transition function are dummies. `ObjSpec.iface Op Resp` is this dummy specification
(stateless, every operation returns `default`). CSLib's `taskObj In Out` is an instance
(`taskObj_eq_iface`).
-/

@[expose] public section

namespace Cslib.SharedMemory

/-- The dummy sequential specification with operations `Op` and responses `Resp`: no state,
every operation returns `default`. Used for objects specified by properties of executions
rather than sequentially. -/
@[reducible] def ObjSpec.iface (Op Resp : Type) [Inhabited Resp] : ObjSpec where
  State := Unit
  Op := Op
  Resp := Resp
  init := ()
  δ _ _ := ((), default)

/-- The dummy object of a task is the interface-only object of its input and output types. -/
lemma taskObj_eq_iface (In Out : Type) [Inhabited Out] :
    taskObj In Out = ObjSpec.iface In Out := rfl

end Cslib.SharedMemory
