/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init

/-!
# Herlihy–Wing histories

Histories of concurrent objects in the style of Herlihy and Wing: a *history* is a finite
sequence of invocation events `inv p x o` (process `p` invokes operation `o` on object `x`) and
response events `res p x r`.

This framework complements the shared-memory model `Cslib.SharedMemory`: it is purely
history-level (there are no implementations, only histories), and it allows several objects,
so that history-level notions such as extensions, `complete(H)`, equivalence, object
subhistories and locality can be stated. The single-object linearizability
`Cslib.SharedMemory.IsLinearization` of executions of `Cslib.SharedMemory` is exactly the
amended definition `Cslib.SharedMemory.HerlihyWing.Linearizable` (see
`Cslib.SharedMemory.HerlihyWing.cslib_linearizable_iff`). Several names of this namespace
(`OpId`, `WellFormed`, `Precedes`, `Invoked`, `Completed`, …) shadow the corresponding notions
of `Cslib.SharedMemory`.

## Main definitions

* `restrictP H p` (`H|P`), `restrictX H x` (`H|x`), `Equiv H H'` (equal process subhistories).
* `OpRec`, `seqHist M`: complete sequential histories are lists of (invocation, matching
  response) pairs; `IsSeq` (sequential: pairs, except possibly one last pending invocation),
  `WellFormed` (every process subhistory is sequential).
* `IsExtension H H'`: `H'` is obtained by appending responses to pending invocations.
* `complete H`: `H` without its pending invocations.
* `SeqSpec`, `Legal`: sequential specifications (sets of single-object sequential histories,
  one set per object) and legal sequential histories.
* Operation instances are identified by `OpId` = `(p, x, k)`: the `k`-th operation of process
  `p` on object `x`. This identification is invariant under restriction to an object or a
  process, so it identifies operations of `H`, of `H'`, of `complete(H')`, of `H|x` and of an
  equivalent sequential history `S` exactly as Herlihy and Wing do implicitly.
* `Invoked`, `Completed`, `opOf`, `resOf`, `Precedes H a b` (the response of `a` occurs before
  the invocation of `b`), `RT H a b` (`a <_H b`: real-time order on *operations*, i.e.
  completed instances, of `H`).
* `idsOf M`: the identities of the operations of the sequential history `seqHist M`.

## References

* [M. P. Herlihy, J. M. Wing, *Linearizability: A Correctness Condition for Concurrent
  Objects*][HerlihyWing1990]
* [G. Sela, M. Herlihy, E. Petrank, *Brief Announcement: Linearizability: A
  Typo*][SelaHerlihyPetrank2021]
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

/-- Events of a history. -/
inductive Event (P X Op Res : Type) where
  /-- Process `p` invokes operation `o` on object `x`. -/
  | inv (p : P) (x : X) (o : Op)
  /-- Process `p` receives response `r` from object `x`. -/
  | res (p : P) (x : X) (r : Res)
  deriving DecidableEq

variable {P X Op Res : Type}

namespace Event

/-- The process of an event. -/
def proc : Event P X Op Res → P
  | inv p _ _ => p
  | res p _ _ => p

/-- The object of an event. -/
def obj : Event P X Op Res → X
  | inv _ x _ => x
  | res _ x _ => x

/-- Is this a response event? -/
def isRes : Event P X Op Res → Bool
  | inv .. => false
  | res .. => true

@[simp] lemma proc_inv (p : P) (x : X) (o : Op) : (inv p x o : Event P X Op Res).proc = p := rfl
@[simp] lemma proc_res (p : P) (x : X) (r : Res) : (res p x r : Event P X Op Res).proc = p := rfl
@[simp] lemma obj_inv (p : P) (x : X) (o : Op) : (inv p x o : Event P X Op Res).obj = x := rfl
@[simp] lemma obj_res (p : P) (x : X) (r : Res) : (res p x r : Event P X Op Res).obj = x := rfl
@[simp] lemma isRes_inv (p : P) (x : X) (o : Op) :
    (inv p x o : Event P X Op Res).isRes = false := rfl
@[simp] lemma isRes_res (p : P) (x : X) (r : Res) :
    (res p x r : Event P X Op Res).isRes = true := rfl

variable [DecidableEq P] [DecidableEq X]

/-- The operation invoked by `p` on `x` at this event, if any. -/
def invOf (p : P) (x : X) : Event P X Op Res → Option Op
  | inv q y o => if q = p ∧ y = x then some o else none
  | res .. => none

/-- The response returned to `p` by `x` at this event, if any. -/
def resOf (p : P) (x : X) : Event P X Op Res → Option Res
  | inv .. => none
  | res q y r => if q = p ∧ y = x then some r else none

@[simp] lemma invOf_inv (p q : P) (x y : X) (o : Op) :
    (inv q y o : Event P X Op Res).invOf p x = if q = p ∧ y = x then some o else none := rfl
@[simp] lemma invOf_res (p q : P) (x y : X) (r : Res) :
    (res q y r : Event P X Op Res).invOf p x = none := rfl
@[simp] lemma resOf_inv (p q : P) (x y : X) (o : Op) :
    (inv q y o : Event P X Op Res).resOf p x = none := rfl
@[simp] lemma resOf_res (p q : P) (x y : X) (r : Res) :
    (res q y r : Event P X Op Res).resOf p x = if q = p ∧ y = x then some r else none := rfl

end Event

/-- Histories: finite sequences of events. -/
abbrev History (P X Op Res : Type) := List (Event P X Op Res)

/-- An operation record of a sequential history: an invocation together with its matching
response. -/
structure OpRec (P X Op Res : Type) where
  /-- The process. -/
  p : P
  /-- The object. -/
  x : X
  /-- The operation (with its arguments). -/
  o : Op
  /-- The response. -/
  r : Res
  deriving DecidableEq

/-- The two events of an operation record. -/
def OpRec.events (e : OpRec P X Op Res) : History P X Op Res := [.inv e.p e.x e.o, .res e.p e.x e.r]

/-- The complete sequential history consisting of the given operations, one after another. -/
def seqHist (M : List (OpRec P X Op Res)) : History P X Op Res := M.flatMap OpRec.events

/-- A history is *sequential* if it comprises a sequence of pairs of an invocation and a matching
response, except possibly a last invocation without a matching response. -/
def IsSeq (s : History P X Op Res) : Prop :=
  ∃ M : List (OpRec P X Op Res), s = seqHist M ∨ ∃ p x o, s = seqHist M ++ [.inv p x o]

/-- Identity of an operation instance: the `k`-th (0-based) operation of process `p` on
object `x`. -/
structure OpId (P X : Type) where
  /-- The process. -/
  p : P
  /-- The object. -/
  x : X
  /-- The index among the operations of `p` on `x`. -/
  k : ℕ
  deriving DecidableEq

/-- A sequential specification: for each object, a set of single-object sequential histories
(the legal ones). -/
abbrev SeqSpec (P X Op Res : Type) := X → Set (History P X Op Res)

variable [DecidableEq P] [DecidableEq X]

/-- The process subhistory `H|p`. -/
def restrictP (H : History P X Op Res) (p : P) : History P X Op Res := H.filter (·.proc = p)

/-- The object subhistory `H|x`. -/
def restrictX (H : History P X Op Res) (x : X) : History P X Op Res := H.filter (·.obj = x)

/-- `H` and `H'` are *equivalent*: they have the same process subhistories. -/
def Equiv (H H' : History P X Op Res) : Prop := ∀ p, restrictP H p = restrictP H' p

/-- A history is *well-formed* if each of its process subhistories is sequential. -/
def WellFormed (H : History P X Op Res) : Prop := ∀ p, IsSeq (restrictP H p)

/-- `H'` is an *extension* of `H`: it is obtained by appending responses (to pending
invocations of `H`; since `H'` is well-formed, each appended response matches a distinct
pending invocation). -/
def IsExtension (H H' : History P X Op Res) : Prop :=
  ∃ R : History P X Op Res, H' = H ++ R ∧ (∀ e ∈ R, e.isRes = true) ∧ WellFormed H'

/-- An event `e` is kept by `complete` if it is a response or if a later event of the same
process follows it (in a well-formed history: if it is an invocation with a matching
response). -/
def keep (e : Event P X Op Res) (later : History P X Op Res) : Bool :=
  e.isRes || later.any (fun f => decide (f.proc = e.proc))

/-- `completeAux β later`: the events of `β` kept by `complete` in `β ++ later`. -/
def completeAux : History P X Op Res → History P X Op Res → History P X Op Res
  | [], _ => []
  | e :: β, later => if keep e (β ++ later) then e :: completeAux β later else completeAux β later

/-- `complete(H)`: the maximal subhistory of `H` without pending invocations. -/
def complete (H : History P X Op Res) : History P X Op Res := completeAux H []

/-- A sequential history is *legal* for the specification if each of its object subhistories
belongs to the sequential specification of that object. -/
def Legal (spec : SeqSpec P X Op Res) (S : History P X Op Res) : Prop :=
  IsSeq S ∧ ∀ x, restrictX S x ∈ spec x

/-! ## Operation instances -/

/-- The operations invoked by `p` on `x`, in order. -/
def opsOf (H : History P X Op Res) (p : P) (x : X) : List Op := H.filterMap (Event.invOf p x)

/-- The responses returned to `p` by `x`, in order. -/
def ressOf (H : History P X Op Res) (p : P) (x : X) : List Res := H.filterMap (Event.resOf p x)

/-- The operation of the instance `a` (if invoked). -/
def opOf (H : History P X Op Res) (a : OpId P X) : Option Op := (opsOf H a.p a.x)[a.k]?

/-- The response of the instance `a` (if completed). -/
def resOf (H : History P X Op Res) (a : OpId P X) : Option Res := (ressOf H a.p a.x)[a.k]?

/-- The instance `a` has been invoked in `H`. -/
def Invoked (H : History P X Op Res) (a : OpId P X) : Prop := a.k < (opsOf H a.p a.x).length

/-- The instance `a` has completed in `H` (it is an *operation* of `H`). -/
def Completed (H : History P X Op Res) (a : OpId P X) : Prop := a.k < (ressOf H a.p a.x).length

instance (H : History P X Op Res) (a : OpId P X) : Decidable (Invoked H a) :=
  inferInstanceAs (Decidable (_ < _))
instance (H : History P X Op Res) (a : OpId P X) : Decidable (Completed H a) :=
  inferInstanceAs (Decidable (_ < _))

/-- The response of `a` occurs in `H` before the invocation of `b` (or `b` is not invoked). -/
def Precedes (H : History P X Op Res) (a b : OpId P X) : Prop :=
  ∃ β γ, H = β ++ γ ∧ Completed β a ∧ ¬ Invoked β b

/-- Real-time order `a <_H b` on the operations of `H`: both are operations of `H`
(completed), and `a` ends before `b` begins. -/
def RT (H : History P X Op Res) (a b : OpId P X) : Prop := Precedes H a b ∧ Completed H b

/-! ## Identities of the operations of a sequential history -/

/-- Number of records of `p` on `x` in `M`. -/
def cnt (M : List (OpRec P X Op Res)) (p : P) (x : X) : ℕ :=
  M.countP (fun e => decide (e.p = p) && decide (e.x = x))

/-- Identities of the records of `M`, given the records `pre` that precede them. -/
def idsGo (pre : List (OpRec P X Op Res)) : List (OpRec P X Op Res) → List (OpId P X)
  | [] => []
  | e :: M => ⟨e.p, e.x, cnt pre e.p e.x⟩ :: idsGo (pre ++ [e]) M

/-- The identities of the operations of the sequential history `seqHist M`, in order. -/
def idsOf (M : List (OpRec P X Op Res)) : List (OpId P X) := idsGo [] M

end Cslib.SharedMemory.HerlihyWing
