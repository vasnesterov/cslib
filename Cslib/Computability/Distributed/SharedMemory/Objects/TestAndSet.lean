/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Spec

/-!
# Test&set objects

Sequential specifications (`ObjSpec`) of test&set objects. Bits are `Bool` with `false` = 0,
initially `false`; `tas` sets the bit and returns its old value.

* `tasObj` — (non-readable) test&set: the only operation is `tas`;
* `rtasObj` — readable test&set (`tas` / `read`);
* `mtasObj` — readable multi-shot test&set (`tas` / `read` / `reset`).
-/

@[expose] public section

namespace Cslib.SharedMemory

/-- (Non-readable) test&set: the only operation sets the bit and returns its old value. -/
abbrev tasObj : ObjSpec where
  State := Bool
  Op := Unit
  Resp := Bool
  init := false
  δ q _ := (true, q)

@[simp] lemma tasObj_δ (q : Bool) (o : Unit) : tasObj.δ q o = (true, q) := rfl

/-- Operations of a readable test&set. -/
inductive RTASOp where
  | tas
  | read
  deriving DecidableEq

/-- Readable test&set. -/
abbrev rtasObj : ObjSpec where
  State := Bool
  Op := RTASOp
  Resp := Bool
  init := false
  δ q
    | .tas => (true, q)
    | .read => (q, q)

@[simp] lemma rtasObj_tas (q : Bool) : rtasObj.δ q .tas = (true, q) := rfl

@[simp] lemma rtasObj_read (q : Bool) : rtasObj.δ q .read = (q, q) := rfl

/-- Operations of a readable multi-shot test&set. -/
inductive MTASOp where
  | tas
  | read
  | reset
  deriving DecidableEq

/-- Readable multi-shot test&set: `reset` sets the bit back to `false` (and returns `false`). -/
abbrev mtasObj : ObjSpec where
  State := Bool
  Op := MTASOp
  Resp := Bool
  init := false
  δ q
    | .tas => (true, q)
    | .read => (q, q)
    | .reset => (false, false)

@[simp] lemma mtasObj_tas (q : Bool) : mtasObj.δ q .tas = (true, q) := rfl

@[simp] lemma mtasObj_read (q : Bool) : mtasObj.δ q .read = (q, q) := rfl

@[simp] lemma mtasObj_reset (q : Bool) : mtasObj.δ q .reset = (false, false) := rfl

end Cslib.SharedMemory
