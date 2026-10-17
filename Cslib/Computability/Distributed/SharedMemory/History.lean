/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Spec
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Range
public import Mathlib.Data.List.Infix

/-!
# Histories and linearizability

Executions of a shared-memory implementation are recorded as lists of *labels*
(`Label P A`): invocations `inv p o`, responses `ret p r` and internal steps `tau p` (a step of
process `p` that accesses a base object). The *history* of an execution consists of its
invocations and responses; all notions in this file only look at those.

Operation instances are identified by `OpId P = P × ℕ`: `(p, k)` is the `k`-th operation
(0-based) invoked by process `p`. In a well-formed history the `k`-th response of `p` belongs to
the `k`-th invocation of `p`, so

* `opOf α (p, k)` is the operation of the `k`-th invocation of `p`,
* `respOf α (p, k)` is the `k`-th response of `p` (if any),
* `Invoked α (p, k)` / `Completed α (p, k)` say that it was invoked / has returned,
* `Precedes α a b` is the real-time order: `a` returns before `b` is invoked.

A *linearization* (Herlihy–Wing) of `α` is a list of operation instances, with their operations,
that contains every completed operation and possibly some pending ones, respects the real-time
order and is legal for the sequential specification (completed operations get their actual
responses). This is the usual "permutation of a completion" definition, phrased with explicit
operation identities.

-/

@[expose] public section

namespace Cslib.SharedMemory

variable {P : Type} {A : ObjSpec}

/-- Labels of executions: invocation, response, and an internal step (base-object access). -/
inductive Label (P : Type) (A : ObjSpec) where
  /-- Process `p` invokes high-level operation `o`. -/
  | inv (p : P) (o : A.Op)
  /-- Process `p` returns response `r` of its pending high-level operation. -/
  | ret (p : P) (r : A.Resp)
  /-- Process `p` takes a step accessing a base object. -/
  | tau (p : P)

namespace Label

/-- The process taking a step. -/
def proc : Label P A → P
  | inv p _ => p
  | ret p _ => p
  | tau p => p

/-- Steps (as opposed to invocations): internal steps and responses. -/
def IsStep : Label P A → Prop
  | inv _ _ => False
  | _ => True

variable [DecidableEq P]

/-- The operation invoked by `p` at this label, if any. -/
def invOf (p : P) : Label P A → Option A.Op
  | inv q o => if q = p then some o else none
  | _ => none

/-- The response returned by `p` at this label, if any. -/
def retOf (p : P) : Label P A → Option A.Resp
  | ret q r => if q = p then some r else none
  | _ => none

@[simp] lemma invOf_inv (p q : P) (o : A.Op) :
    (inv q o : Label P A).invOf p = if q = p then some o else none := rfl
@[simp] lemma invOf_ret (p q : P) (r : A.Resp) : (ret q r : Label P A).invOf p = none := rfl
@[simp] lemma invOf_tau (p q : P) : (tau q : Label P A).invOf p = none := rfl
@[simp] lemma retOf_inv (p q : P) (o : A.Op) : (inv q o : Label P A).retOf p = none := rfl
@[simp] lemma retOf_ret (p q : P) (r : A.Resp) :
    (ret q r : Label P A).retOf p = if q = p then some r else none := rfl
@[simp] lemma retOf_tau (p q : P) : (tau q : Label P A).retOf p = none := rfl

lemma invOf_eq_none_of_proc_ne {p : P} {ℓ : Label P A} (h : ℓ.proc ≠ p) : ℓ.invOf p = none := by
  cases ℓ <;> simp_all [proc]

lemma retOf_eq_none_of_proc_ne {p : P} {ℓ : Label P A} (h : ℓ.proc ≠ p) : ℓ.retOf p = none := by
  cases ℓ <;> simp_all [proc]

end Label

/-- Identity of an operation instance: `(p, k)` is the `k`-th operation invoked by `p`. -/
abbrev OpId (P : Type) := P × ℕ

section History

variable [DecidableEq P]

/-- The operations invoked by `p` in `α`, in order. -/
def opsOf (α : List (Label P A)) (p : P) : List A.Op := α.filterMap (Label.invOf p)

/-- The responses returned by `p` in `α`, in order. -/
def respsOf (α : List (Label P A)) (p : P) : List A.Resp := α.filterMap (Label.retOf p)

/-- The operation of the instance `x`. -/
def opOf (α : List (Label P A)) (x : OpId P) : Option A.Op := (opsOf α x.1)[x.2]?

/-- The response of the instance `x` (if it has returned). -/
def respOf (α : List (Label P A)) (x : OpId P) : Option A.Resp := (respsOf α x.1)[x.2]?

/-- The instance `x` has been invoked in `α`. -/
def Invoked (α : List (Label P A)) (x : OpId P) : Prop := x.2 < (opsOf α x.1).length

/-- The instance `x` has returned in `α`. -/
def Completed (α : List (Label P A)) (x : OpId P) : Prop := x.2 < (respsOf α x.1).length

/-- Real-time order: `a` returns before `b` is invoked. -/
def Precedes (α : List (Label P A)) (a b : OpId P) : Prop :=
  ∃ β γ, α = β ++ γ ∧ Completed β a ∧ ¬ Invoked β b

@[simp] lemma opsOf_nil (p : P) : opsOf ([] : List (Label P A)) p = [] := rfl
@[simp] lemma respsOf_nil (p : P) : respsOf ([] : List (Label P A)) p = [] := rfl

@[simp] lemma opsOf_append (α β : List (Label P A)) (p : P) :
    opsOf (α ++ β) p = opsOf α p ++ opsOf β p := by simp [opsOf]

@[simp] lemma respsOf_append (α β : List (Label P A)) (p : P) :
    respsOf (α ++ β) p = respsOf α p ++ respsOf β p := by simp [respsOf]

@[simp] lemma opsOf_cons (ℓ : Label P A) (α : List (Label P A)) (p : P) :
    opsOf (ℓ :: α) p = (ℓ.invOf p).toList ++ opsOf α p := by
  cases h : ℓ.invOf p <;> simp [opsOf, h]

@[simp] lemma respsOf_cons (ℓ : Label P A) (α : List (Label P A)) (p : P) :
    respsOf (ℓ :: α) p = (ℓ.retOf p).toList ++ respsOf α p := by
  cases h : ℓ.retOf p <;> simp [respsOf, h]

lemma opsOf_eq_nil_of_proc_ne {α : List (Label P A)} {p : P} (h : ∀ ℓ ∈ α, ℓ.proc ≠ p) :
    opsOf α p = [] := by
  simp only [opsOf, List.filterMap_eq_nil_iff]
  exact fun ℓ hℓ => Label.invOf_eq_none_of_proc_ne (h ℓ hℓ)

lemma respsOf_eq_nil_of_proc_ne {α : List (Label P A)} {p : P} (h : ∀ ℓ ∈ α, ℓ.proc ≠ p) :
    respsOf α p = [] := by
  simp only [respsOf, List.filterMap_eq_nil_iff]
  exact fun ℓ hℓ => Label.retOf_eq_none_of_proc_ne (h ℓ hℓ)

lemma Invoked.mono {α β : List (Label P A)} {x : OpId P} (h : Invoked α x) :
    Invoked (α ++ β) x := by
  simp only [Invoked, opsOf_append, List.length_append] at *; omega

lemma Completed.mono {α β : List (Label P A)} {x : OpId P} (h : Completed α x) :
    Completed (α ++ β) x := by
  simp only [Completed, respsOf_append, List.length_append] at *; omega

lemma opOf_append_of_invoked {α β : List (Label P A)} {x : OpId P} (h : Invoked α x) :
    opOf (α ++ β) x = opOf α x := by
  simp only [opOf, opsOf_append]; exact List.getElem?_append_left h

lemma respOf_append_of_completed {α β : List (Label P A)} {x : OpId P} (h : Completed α x) :
    respOf (α ++ β) x = respOf α x := by
  simp only [respOf, respsOf_append]; exact List.getElem?_append_left h

lemma Precedes.mono {α β : List (Label P A)} {a b : OpId P} (h : Precedes α a b) :
    Precedes (α ++ β) a b := by
  obtain ⟨β₁, γ, rfl, h1, h2⟩ := h
  exact ⟨β₁, γ ++ β, by simp, h1, h2⟩

lemma Precedes.completed {α : List (Label P A)} {a b : OpId P} (h : Precedes α a b) :
    Completed α a := by
  obtain ⟨β, γ, rfl, h1, -⟩ := h
  exact h1.mono

/-- Real-time precedence in an extension, towards an operation invoked before the extension,
already holds before the extension. -/
lemma Precedes.of_append_of_invoked {α β : List (Label P A)} {a b : OpId P}
    (h : Precedes (α ++ β) a b) (hb : Invoked α b) : Precedes α a b := by
  obtain ⟨β₁, γ, hsplit, h1, h2⟩ := h
  rcases List.append_eq_append_iff.1 hsplit with ⟨a', rfl, -⟩ | ⟨c', rfl, -⟩
  · exact absurd hb.mono h2
  · exact ⟨β₁, c', rfl, h1, h2⟩

/-- Well-formedness of a history: every process alternates invocations and responses, starting
with an invocation. -/
def WellFormed (α : List (Label P A)) : Prop :=
  ∀ β ℓ γ, α = β ++ ℓ :: γ → ∀ p,
    (ℓ.invOf p ≠ none → (opsOf β p).length = (respsOf β p).length) ∧
    (ℓ.retOf p ≠ none → (opsOf β p).length = (respsOf β p).length + 1)

/-! ## Linearizations -/

/-- Legality of a sequential history (list of instances with their operations) started from
state `q`: every completed instance in the list gets the response the specification
prescribes. -/
def SeqOK (α : List (Label P A)) : A.State → List (OpId P × A.Op) → Prop
  | _, [] => True
  | q, (x, o) :: L => (∀ r, respOf α x = some r → (A.δ q o).2 = r) ∧ SeqOK α (A.δ q o).1 L

/-- `L` is a linearization of (the history of) `α`. -/
structure IsLinearization (α : List (Label P A)) (L : List (OpId P × A.Op)) : Prop where
  nodup : (L.map Prod.fst).Nodup
  op_eq : ∀ y ∈ L, opOf α y.1 = some y.2
  complete : ∀ a, Completed α a → a ∈ L.map Prod.fst
  realtime : ∀ a b, Precedes α a b → b ∈ L.map Prod.fst → [a, b].Sublist (L.map Prod.fst)
  seq : SeqOK α A.init L

/-- The abstract state after a sequential history (paper: `state(H)`). -/
def linState (L : List (OpId P × A.Op)) : A.State := A.runOps A.init (L.map Prod.snd)

end History

end Cslib.SharedMemory
