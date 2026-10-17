/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Sequential specifications of shared objects

An *abstract object* (Herlihy–Wing; Attiya–Welch) is given by its sequential specification:
a type of states with a designated initial state, a type of operations (including their
arguments), a type of responses and a deterministic transition function
`δ : State → Op → State × Resp`.

The same structure is used both for the *implemented* (high-level) object and for the *base*
objects of an implementation (registers, CAS, …).

*Nondeterministic* sequential specifications (`NSpec Op Resp`: a transition relation
`Step q o r q'`, e.g. sets whose `take` returns an arbitrary element, or relaxed queues) are used
as correctness conditions only; `NSpec.Legal q l` is the legality of a sequence of
(operation, response) pairs from `q`, and `ObjSpec.toNSpec` views a deterministic specification
as a nondeterministic one.
-/

@[expose] public section

namespace Cslib.SharedMemory

/-- Sequential specification of a deterministic object. -/
structure ObjSpec where
  /-- States of the object. -/
  State : Type
  /-- Operations (with their arguments). -/
  Op : Type
  /-- Responses. -/
  Resp : Type
  /-- The initial state. -/
  init : State
  /-- The (deterministic) sequential specification. -/
  δ : State → Op → State × Resp

namespace ObjSpec

variable (A : ObjSpec)

/-- The state reached from `q` by applying the operations `os` in order. -/
def runOps (q : A.State) (os : List A.Op) : A.State :=
  os.foldl (fun q o => (A.δ q o).1) q

@[simp] lemma runOps_nil (q : A.State) : A.runOps q [] = q := rfl

@[simp] lemma runOps_cons (q : A.State) (o : A.Op) (os : List A.Op) :
    A.runOps q (o :: os) = A.runOps (A.δ q o).1 os := rfl

lemma runOps_append (q : A.State) (os os' : List A.Op) :
    A.runOps q (os ++ os') = A.runOps (A.runOps q os) os' := by
  simp [runOps, List.foldl_append]

/-- An operation is *read-only* if it never changes the state. -/
def ReadOnly (o : A.Op) : Prop := ∀ q, (A.δ q o).1 = q

/-- An operation is *state-changing* if it changes some state (paper: there are `q ≠ q'` such
that `o` moves the object from `q` to `q'`). -/
def StateChanging (o : A.Op) : Prop := ∃ q, (A.δ q o).1 ≠ q

lemma readOnly_iff_not_stateChanging (o : A.Op) : A.ReadOnly o ↔ ¬ A.StateChanging o := by
  simp [ReadOnly, StateChanging]

/-- Running a list of read-only operations does not change the state. -/
lemma runOps_of_readOnly (q : A.State) (os : List A.Op) (h : ∀ o ∈ os, A.ReadOnly o) :
    A.runOps q os = q := by
  induction os generalizing q with
  | nil => rfl
  | cons o os ih =>
    simp only [runOps_cons]
    rw [h o (by simp)]
    exact ih q (fun o' ho' => h o' (by simp [ho']))

/-- Read-only operations can be dropped from an operation sequence without changing the
resulting state (stated for a list of decorated operations `l` with `f` extracting the
operation). -/
lemma runOps_map_filter {X : Type} (q : A.State) (l : List X) (f : X → A.Op) (pr : X → Bool)
    (h : ∀ x ∈ l, pr x = false → A.ReadOnly (f x)) :
    A.runOps q ((l.filter pr).map f) = A.runOps q (l.map f) := by
  induction l generalizing q with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : pr x = true
    · simp [hx, ih _ (fun x' hx' => h x' (by simp [hx']))]
    · have hro := h x (by simp) (by simpa using hx)
      simp only [List.filter_cons, hx, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        runOps_cons, hro q]
      exact ih q (fun x' hx' => h x' (by simp [hx']))

end ObjSpec

/-! ## Standard objects -/

/-- Operations of a read/write register over values `V`. -/
inductive RWOp (V : Type) where
  | read
  | write (v : V)
  deriving DecidableEq

/-- A read/write register over values `V` with initial value `v₀`. The response of a `write`
is the written value (a dummy). -/
abbrev register (V : Type) (v₀ : V) : ObjSpec where
  State := V
  Op := RWOp V
  Resp := V
  init := v₀
  δ q
    | .read => (q, q)
    | .write v => (v, v)

/-- A binary register (values `Bool`, initially `false`). -/
abbrev binaryRegister (b₀ : Bool := false) : ObjSpec := register Bool b₀

@[simp] lemma register_read (V : Type) (v₀ : V) (q : V) :
    (register V v₀).δ q .read = (q, q) := rfl

@[simp] lemma register_write (V : Type) (v₀ : V) (q v : V) :
    (register V v₀).δ q (.write v) = (v, v) := rfl

/-- Operations of a compare-and-swap object (which also supports read and write). -/
inductive CASOp (V : Type) where
  | read
  | write (v : V)
  | cas (old new : V)

/-- A compare-and-swap object over `V`; responses are `Sum V Bool` (value for `read`,
success flag for `cas`, `true` for `write`). -/
abbrev casObject (V : Type) [DecidableEq V] (v₀ : V) : ObjSpec where
  State := V
  Op := CASOp V
  Resp := V ⊕ Bool
  init := v₀
  δ q
    | .read => (q, .inl q)
    | .write v => (v, .inr true)
    | .cas old new => if q = old then (new, .inr true) else (q, .inr false)

/-- The single-writer single-reader discipline: process `w` only writes, process `r` only reads,
other processes invoke nothing. -/
def RWOp.SWSR {V : Type} {P : Type} (w r : P) (p : P) (o : RWOp V) : Prop :=
  (p = w ∧ ∃ v, o = .write v) ∨ (p = r ∧ o = .read)

end Cslib.SharedMemory

/-! ### Nondeterministic sequential specifications -/

namespace Cslib.SharedMemory

/-- A *nondeterministic* sequential specification over operations `Op` and responses `Resp`:
`Step q o r q'` says that applying `o` in state `q` may return `r` and move to `q'`. -/
structure NSpec (Op Resp : Type) where
  /-- States. -/
  State : Type
  /-- The initial state. -/
  init : State
  /-- The transition relation. -/
  Step : State → Op → Resp → State → Prop

namespace NSpec

variable {Op Resp : Type} (S : NSpec Op Resp)

/-- A sequence of operations with responses is legal from state `q`. -/
def Legal : S.State → List (Op × Resp) → Prop
  | _, [] => True
  | q, (o, r) :: l => ∃ q', S.Step q o r q' ∧ Legal q' l

@[simp] lemma legal_nil (q : S.State) : S.Legal q [] := trivial

@[simp] lemma legal_cons (q : S.State) (o : Op) (r : Resp) (l : List (Op × Resp)) :
    S.Legal q ((o, r) :: l) ↔ ∃ q', S.Step q o r q' ∧ S.Legal q' l := Iff.rfl

end NSpec

/-- The deterministic specification `A` as a nondeterministic one. -/
def ObjSpec.toNSpec (A : ObjSpec) : NSpec A.Op A.Resp where
  State := A.State
  init := A.init
  Step q o r q' := A.δ q o = (q', r)

@[simp] lemma ObjSpec.toNSpec_step (A : ObjSpec) (q : A.State) (o : A.Op) (r : A.Resp)
    (q' : A.State) : A.toNSpec.Step q o r q' ↔ A.δ q o = (q', r) := Iff.rfl

end Cslib.SharedMemory
