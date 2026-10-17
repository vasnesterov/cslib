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
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

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

## Further API

* `PrefixClosed E`: a set of executions closed under prefixes (usage disciplines such as
  one-shot executions);
* `Label.isTauOf p`: `ℓ` is an internal step of `p` (as a `Bool`, for counting steps);
* `curOp α p`: the *current* operation instance of `p` (the instance of its pending operation,
  if any, otherwise of its next one); it has not completed (`not_completed_curOp`);
* `opOf_append_of_eq_some`, `respOf_append_of_eq_some`: the operation/response of an instance
  does not change when the execution is extended; `opsOf_concat`, `respsOf_concat`,
  `opOf_concat_inv` and their `_of_ne` versions: appending one label;
* `opsOf_prefix`, `respsOf_prefix`, `WellFormed.of_append`: prefixes;
* `linState_append`, `linState_concat`: the abstract state after a concatenation of sequential
  histories.

## Appending one label, real-time order, counting invocations

Bookkeeping lemmas for invariant proofs over executions extended one label at a time.

* `Label.eq_inv_of_invOf_eq_some`, `Label.eq_ret_of_retOf_eq_some`: recovering a label.
* `opsOf_append_tau`, `opsOf_append_ret`, `respsOf_append_inv`, `respsOf_append_tau`,
  `respsOf_append_ret_of_ne`, `opOf_append_tau`, `opOf_append_ret`: operations/responses after
  appending a label of a given shape.
* `opOf_concat_cases`, `respOf_concat_cases`: an operation (response) known after appending one
  label was known before, or it is the appended label.
* `completed_append_ret`, `completed_append_ret_of_ne`, `completed_append_of_not_ret`,
  `respOf_append_ret_of_ne`: completed instances after appending one label.
* `precedes_concat`, `Precedes.of_concat_of_not_ret`, `not_precedes_append`: real-time order
  after appending labels.
* `opsOf_filter_proc`, `respsOf_filter_proc`: restricting an execution to the labels of `p`.
* `Label.isInv`, `invCount`, `invCount_eq_sum`: the number of invocations of an execution.

## Well-formed histories, real-time order and invocation order

* `WellFormed.counts`, `WellFormed.resps_le_ops`, `WellFormed.invoked_of_completed`: invocation
  and response counts in well-formed histories;
* `WellFormed.append_singleton`, `WellFormed.append_inv`, `WellFormed.append_ret`: extending a
  well-formed history by one label;
* `Precedes.trans`, `Precedes.lt_of_proc` (program order),
  `Precedes.completed_of_append_singleton`, `Precedes.not_of_invoked`,
  `precedes_append_iff_of_invoked`, `precedes_append_inv_iff`: real-time order;
* `invIdsFrom`, `invIds`: the invoked instances in invocation order (`mem_invIds`,
  `nodup_invIds`, `invIdsFrom_append` with the counters `invCountFrom`); real-time order implies
  invocation order (`Precedes.sublist_invIds`);
* `completed_iff_respOf`, `respOf_append_ret`: completed instances and responses.

## Nondeterministic specifications

`IsNLinearization S α L` is linearizability with respect to a nondeterministic specification
`S : NSpec A.Op A.Resp`; linearizations carry the responses of the linearized operations (pending
ones get the responses chosen by the linearization). For deterministic specifications the two
notions agree: `IsLinearization.isNLinearization_annotate` (annotate a linearization with the
responses of the specification), `IsNLinearization.isLinearization_map` (forget the responses),
`exists_isLinearization_iff`.
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

namespace Cslib.SharedMemory

variable {P : Type} {A : ObjSpec}

/-- A set of finite executions that is closed under taking prefixes. -/
def PrefixClosed (E : List (Label P A) → Prop) : Prop :=
  ∀ α β, E (α ++ β) → E α

lemma PrefixClosed.of_prefix {E : List (Label P A) → Prop} (hE : PrefixClosed E)
    {α β : List (Label P A)} (h : α <+: β) (hβ : E β) : E α := by
  obtain ⟨γ, rfl⟩ := h; exact hE α γ hβ

lemma prefixClosed_true : PrefixClosed (fun _ : List (Label P A) => True) :=
  fun _ _ _ => trivial

variable [DecidableEq P]

namespace Label

/-- `ℓ` is an internal step (base-object access) of `p`. -/
def isTauOf (p : P) : Label P A → Bool
  | .tau q => decide (q = p)
  | _ => false

@[simp] lemma isTauOf_tau (p q : P) : (tau q : Label P A).isTauOf p = decide (q = p) := rfl
@[simp] lemma isTauOf_inv (p q : P) (o : A.Op) : (inv q o : Label P A).isTauOf p = false := rfl
@[simp] lemma isTauOf_ret (p q : P) (r : A.Resp) : (ret q r : Label P A).isTauOf p = false := rfl

lemma isTauOf_eq_true_iff {p : P} {ℓ : Label P A} : ℓ.isTauOf p = true ↔ ℓ = .tau p := by
  cases ℓ <;> simp [eq_comm]

end Label

/-! ### The current operation instance of a process -/

/-- The current operation instance of `p` after `α`: the instance of its pending operation if
there is one, otherwise the instance of its next operation. -/
abbrev curOp (α : List (Label P A)) (p : P) : OpId P := (p, (respsOf α p).length)

@[simp] lemma curOp_nil (p : P) : curOp ([] : List (Label P A)) p = (p, 0) := rfl

@[simp] lemma curOp_append_inv (α : List (Label P A)) (p q : P) (o : A.Op) :
    curOp (α ++ [.inv p o]) q = curOp α q := by
  simp [curOp]

@[simp] lemma curOp_append_tau (α : List (Label P A)) (p q : P) :
    curOp (α ++ [.tau p]) q = curOp α q := by
  simp [curOp]

@[simp] lemma curOp_append_ret_self (α : List (Label P A)) (p : P) (r : A.Resp) :
    curOp (α ++ [.ret p r]) p = (p, (respsOf α p).length + 1) := by
  simp [curOp]

lemma curOp_append_ret_of_ne (α : List (Label P A)) {p q : P} (r : A.Resp) (h : p ≠ q) :
    curOp (α ++ [.ret p r]) q = curOp α q := by
  simp [curOp, h]

lemma curOp_append_of_proc_ne (α : List (Label P A)) {ℓ : Label P A} {q : P}
    (h : ℓ.proc ≠ q) : curOp (α ++ [ℓ]) q = curOp α q := by
  simp [curOp, Label.retOf_eq_none_of_proc_ne h]

/-- The current operation instance of a process has not completed. -/
@[simp] lemma not_completed_curOp (α : List (Label P A)) (p : P) :
    ¬ Completed α (curOp α p) := by
  simp [Completed]

/-! ### Operations and responses of instances in extensions -/

lemma Invoked.of_opOf_eq_some {α : List (Label P A)} {x : OpId P} {o : A.Op}
    (h : opOf α x = some o) : Invoked α x := by
  simp only [opOf] at h; exact (List.getElem?_eq_some_iff.1 h).1

lemma Completed.of_respOf_eq_some {α : List (Label P A)} {x : OpId P} {r : A.Resp}
    (h : respOf α x = some r) : Completed α x := by
  simp only [respOf] at h; exact (List.getElem?_eq_some_iff.1 h).1

lemma opOf_append_of_eq_some {α : List (Label P A)} {x : OpId P} {o : A.Op}
    (h : opOf α x = some o) (β : List (Label P A)) : opOf (α ++ β) x = some o := by
  rw [opOf_append_of_invoked (Invoked.of_opOf_eq_some h), h]

lemma respOf_append_of_eq_some {α : List (Label P A)} {x : OpId P} {r : A.Resp}
    (h : respOf α x = some r) (β : List (Label P A)) : respOf (α ++ β) x = some r := by
  rw [respOf_append_of_completed (Completed.of_respOf_eq_some h), h]

/-! ### Operations and responses after appending one label -/

/-- The operations of `p` after appending `ℓ`: those before, plus `ℓ`'s invocation by `p`. -/
lemma opsOf_concat (α : List (Label P A)) (ℓ : Label P A) (p : P) :
    opsOf (α ++ [ℓ]) p = opsOf α p ++ (ℓ.invOf p).toList := by
  rw [opsOf_append]; cases h : ℓ.invOf p <;> simp [opsOf, h]

/-- The responses of `p` after appending `ℓ`: those before, plus `ℓ`'s response to `p`. -/
lemma respsOf_concat (α : List (Label P A)) (ℓ : Label P A) (p : P) :
    respsOf (α ++ [ℓ]) p = respsOf α p ++ (ℓ.retOf p).toList := by
  rw [respsOf_append]; cases h : ℓ.retOf p <;> simp [respsOf, h]

/-- Appending a label that is not an invocation of `q` does not change `q`'s operations. -/
lemma opsOf_concat_of_ne {α : List (Label P A)} {ℓ : Label P A} {q : P}
    (hℓ : ∀ o, ℓ ≠ .inv q o) : opsOf (α ++ [ℓ]) q = opsOf α q := by
  cases ℓ with
  | inv q' o =>
    have : q' ≠ q := fun h => hℓ o (by rw [h])
    simp [this]
  | _ => simp

/-- Appending a label that is not a response of `q` does not change `q`'s responses. -/
lemma respsOf_concat_of_ne {α : List (Label P A)} {ℓ : Label P A} {q : P}
    (hℓ : ∀ r, ℓ ≠ .ret q r) : respsOf (α ++ [ℓ]) q = respsOf α q := by
  cases ℓ with
  | ret q' r =>
    have : q' ≠ q := fun h => hℓ r (by rw [h])
    simp [this]
  | _ => simp

/-- Appending a label that is not an invocation of `x.1` does not change the operation of `x`. -/
lemma opOf_concat_of_ne {α : List (Label P A)} {ℓ : Label P A} {x : OpId P}
    (hℓ : ∀ o, ℓ ≠ .inv x.1 o) : opOf (α ++ [ℓ]) x = opOf α x := by
  simp only [opOf, opsOf_concat_of_ne hℓ]

/-- The operation of an instance after appending an invocation: the new invocation is the
operation of `(p, (opsOf α p).length)`; other instances are unchanged. -/
lemma opOf_concat_inv (α : List (Label P A)) (p : P) (o : A.Op) (y : OpId P) :
    opOf (α ++ [.inv p o]) y = if y = (p, (opsOf α p).length) then some o else opOf α y := by
  obtain ⟨q, k⟩ := y
  simp only [opOf, opsOf_append, opsOf_cons, Label.invOf_inv, opsOf_nil, List.append_nil,
    Prod.mk.injEq]
  by_cases hq : p = q
  · subst hq
    simp only [ite_true, Option.toList_some, true_and]
    rcases lt_trichotomy k (opsOf α p).length with h | rfl | h
    · rw [List.getElem?_append_left h, ite_eq_right (by omega)]
    · simp
    · rw [ite_eq_right (by omega), List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by omega)]
  · simp [hq, Ne.symm hq]

/-- Appending a label that is not a response of `x.1` does not change the response of `x`. -/
lemma respOf_concat_of_ne {α : List (Label P A)} {ℓ : Label P A} {x : OpId P}
    (hℓ : ∀ r, ℓ ≠ .ret x.1 r) : respOf (α ++ [ℓ]) x = respOf α x := by
  simp only [respOf, respsOf_concat_of_ne hℓ]

/-- Appending a label that is not a response does not change the responses of instances. -/
lemma respOf_append_of_not_ret {α : List (Label P A)} {ℓ : Label P A}
    (hℓ : ∀ p r, ℓ ≠ .ret p r) (x : OpId P) : respOf (α ++ [ℓ]) x = respOf α x :=
  respOf_concat_of_ne fun r => hℓ x.1 r

/-! ### Prefixes -/

/-- A prefix of a well-formed history is well formed. -/
lemma WellFormed.of_append {α β : List (Label P A)} (h : WellFormed (α ++ β)) : WellFormed α :=
  fun γ ℓ δ hγ p => h γ ℓ (δ ++ β) (by rw [hγ]; simp) p

/-- The operations of a process along a prefix form a prefix. -/
lemma opsOf_prefix {α β : List (Label P A)} (h : α <+: β) (p : P) :
    opsOf α p <+: opsOf β p := by
  obtain ⟨u, rfl⟩ := h; rw [opsOf_append]; exact List.prefix_append _ _

/-- The responses of a process along a prefix form a prefix. -/
lemma respsOf_prefix {α β : List (Label P A)} (h : α <+: β) (p : P) :
    respsOf α p <+: respsOf β p := by
  obtain ⟨u, rfl⟩ := h; rw [respsOf_append]; exact List.prefix_append _ _

end Cslib.SharedMemory

namespace Cslib.SharedMemory

variable {P : Type} {A : ObjSpec}

/-! ### The state after a sequential history -/

@[simp] lemma linState_nil : linState ([] : List (OpId P × A.Op)) = A.init := rfl

lemma linState_append (L M : List (OpId P × A.Op)) :
    linState (L ++ M) = A.runOps (linState L) (M.map Prod.snd) := by
  simp [linState, ObjSpec.runOps_append]

@[simp] lemma linState_concat (L : List (OpId P × A.Op)) (x : OpId P) (o : A.Op) :
    linState (L ++ [(x, o)]) = (A.δ (linState L) o).1 := by
  simp [linState_append]

end Cslib.SharedMemory

/-! ### Linearizability with respect to nondeterministic specifications -/

namespace Cslib.SharedMemory

variable {P : Type} {A : ObjSpec}

section NLin

variable [DecidableEq P]

/-- `L` (instances with their operations and responses) is a linearization of `α` with respect
to the nondeterministic specification `S`: no duplicates, the operations are the invoked ones,
completed instances carry their actual responses and are all present, real-time order is
respected, and the sequence of operations/responses is legal for `S`. Pending instances in `L`
carry the responses chosen by the linearization. -/
structure IsNLinearization (S : NSpec A.Op A.Resp) (α : List (Label P A))
    (L : List (OpId P × A.Op × A.Resp)) : Prop where
  nodup : (L.map Prod.fst).Nodup
  op_eq : ∀ y ∈ L, opOf α y.1 = some y.2.1
  resp_eq : ∀ y ∈ L, ∀ r, respOf α y.1 = some r → y.2.2 = r
  complete : ∀ a, Completed α a → a ∈ L.map Prod.fst
  realtime : ∀ a b, Precedes α a b → b ∈ L.map Prod.fst → [a, b].Sublist (L.map Prod.fst)
  legal : S.Legal S.init (L.map Prod.snd)

end NLin

/-! ## Deterministic specifications -/

namespace ObjSpec

/-- Annotate a deterministic sequential history (run from `q`) with the responses of the
specification. -/
def annotate (A : ObjSpec) : A.State → List (OpId P × A.Op) → List (OpId P × A.Op × A.Resp)
  | _, [] => []
  | q, (x, o) :: L => (x, o, (A.δ q o).2) :: annotate A (A.δ q o).1 L

lemma annotate_append (q : A.State) (L L' : List (OpId P × A.Op)) :
    A.annotate q (L ++ L') = A.annotate q L ++ A.annotate (A.runOps q (L.map Prod.snd)) L' := by
  induction L generalizing q with
  | nil => simp [annotate]
  | cons y L ih => obtain ⟨x, o⟩ := y; simp [annotate, ih]

@[simp] lemma annotate_map_fst (q : A.State) (L : List (OpId P × A.Op)) :
    (A.annotate q L).map Prod.fst = L.map Prod.fst := by
  induction L generalizing q with
  | nil => rfl
  | cons y L ih => obtain ⟨x, o⟩ := y; simp [annotate, ih]

lemma mem_annotate {q : A.State} {L : List (OpId P × A.Op)} {y : OpId P × A.Op × A.Resp}
    (hy : y ∈ A.annotate q L) : (y.1, y.2.1) ∈ L := by
  induction L generalizing q with
  | nil => simp [annotate] at hy
  | cons z L ih =>
    obtain ⟨x, o⟩ := z
    simp only [annotate, List.mem_cons] at hy
    rcases hy with rfl | hy
    · simp
    · exact List.mem_cons_of_mem _ (ih hy)

end ObjSpec

variable [DecidableEq P]

/-- Annotating a linearization with the responses of the specification gives a linearization
with respect to the specification viewed as a nondeterministic one. -/
lemma IsLinearization.isNLinearization_annotate {α : List (Label P A)}
    {L : List (OpId P × A.Op)} (hL : IsLinearization α L) :
    IsNLinearization A.toNSpec α (A.annotate A.init L) := by
  have key : ∀ (q : A.State) (L : List (OpId P × A.Op)), SeqOK α q L →
      (∀ y ∈ A.annotate q L, ∀ r, respOf α y.1 = some r → y.2.2 = r) ∧
      A.toNSpec.Legal q ((A.annotate q L).map Prod.snd) := by
    intro q L h
    induction L generalizing q with
    | nil => exact ⟨by simp [ObjSpec.annotate], trivial⟩
    | cons z L ih =>
      obtain ⟨x, o⟩ := z
      obtain ⟨h1, h2⟩ := h
      obtain ⟨ih1, ih2⟩ := ih _ h2
      refine ⟨?_, ?_⟩
      · intro y hy r hr
        simp only [ObjSpec.annotate, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact h1 r hr
        · exact ih1 y hy r hr
      · simp only [ObjSpec.annotate, List.map_cons]
        exact ⟨_, rfl, ih2⟩
  obtain ⟨k1, k2⟩ := key A.init L hL.seq
  refine ⟨?_, ?_, k1, ?_, ?_, k2⟩
  · rw [ObjSpec.annotate_map_fst]; exact hL.nodup
  · intro y hy; exact hL.op_eq _ (ObjSpec.mem_annotate hy)
  · intro a ha; rw [ObjSpec.annotate_map_fst]; exact hL.complete a ha
  · intro a b hab hb; rw [ObjSpec.annotate_map_fst] at hb ⊢; exact hL.realtime a b hab hb

/-- Forgetting the responses of a linearization with respect to `A.toNSpec` gives a
linearization. -/
lemma IsNLinearization.isLinearization_map {α : List (Label P A)}
    {L : List (OpId P × A.Op × A.Resp)} (hL : IsNLinearization A.toNSpec α L) :
    IsLinearization α (L.map fun y => (y.1, y.2.1)) := by
  have hfst : (L.map fun y => (y.1, y.2.1)).map Prod.fst = L.map Prod.fst := by simp
  have key : ∀ (q : A.State) (L : List (OpId P × A.Op × A.Resp)),
      (∀ y ∈ L, ∀ r, respOf α y.1 = some r → y.2.2 = r) →
      A.toNSpec.Legal q (L.map Prod.snd) → SeqOK α q (L.map fun y => (y.1, y.2.1)) := by
    intro q L h1 h2
    induction L generalizing q with
    | nil => trivial
    | cons y L ih =>
      obtain ⟨x, o, r⟩ := y
      obtain ⟨q', hq', h2⟩ := h2
      change A.δ q o = (q', r) at hq'
      refine ⟨fun r' hr' => ?_, ?_⟩
      · rw [hq']; exact h1 _ (by simp) r' hr'
      · rw [hq']; exact ih q' (fun y hy => h1 y (by simp [hy])) h2
  refine ⟨?_, ?_, ?_, ?_, key _ L hL.resp_eq hL.legal⟩
  · rw [hfst]; exact hL.nodup
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact hL.op_eq z hz
  · intro a ha; rw [hfst]; exact hL.complete a ha
  · intro a b hab hb; rw [hfst] at hb ⊢; exact hL.realtime a b hab hb

/-- For a deterministic specification, an execution has a linearization iff it has one with
respect to the specification viewed as a nondeterministic one. -/
theorem exists_isLinearization_iff {α : List (Label P A)} :
    (∃ L, IsLinearization α L) ↔ ∃ L, IsNLinearization A.toNSpec α L :=
  ⟨fun ⟨_, hL⟩ => ⟨_, hL.isNLinearization_annotate⟩,
    fun ⟨_, hL⟩ => ⟨_, hL.isLinearization_map⟩⟩

end Cslib.SharedMemory

/-! ### Appending one label -/

namespace Cslib.SharedMemory

variable {P : Type} {A : ObjSpec} [DecidableEq P]

namespace Label

/-- A label at which `p` invokes `o` is the invocation `inv p o`. -/
lemma eq_inv_of_invOf_eq_some {ℓ : Label P A} {p : P} {o : A.Op} (h : ℓ.invOf p = some o) :
    ℓ = .inv p o := by
  cases ℓ with
  | inv q o' => simp only [invOf_inv] at h; split_ifs at h with hq; cases h; rw [hq]
  | ret q r => simp at h
  | tau q => simp at h

/-- A label at which `p` returns `r` is the response `ret p r`. -/
lemma eq_ret_of_retOf_eq_some {ℓ : Label P A} {p : P} {r : A.Resp} (h : ℓ.retOf p = some r) :
    ℓ = .ret p r := by
  cases ℓ with
  | ret q r' => simp only [retOf_ret] at h; split_ifs at h with hq; cases h; rw [hq]
  | inv q o => simp at h
  | tau q => simp at h

end Label

/-! ### Operations and responses after appending one label -/

/-- Internal steps do not change the operations of a process. -/
lemma opsOf_append_tau (α : List (Label P A)) (p q : P) :
    opsOf (α ++ [.tau p]) q = opsOf α q := by simp [opsOf_append]

/-- Responses do not change the operations of a process. -/
lemma opsOf_append_ret (α : List (Label P A)) (p q : P) (r : A.Resp) :
    opsOf (α ++ [.ret p r]) q = opsOf α q := by simp [opsOf_append]

/-- Invocations do not change the responses of a process. -/
lemma respsOf_append_inv (α : List (Label P A)) (p q : P) (o : A.Op) :
    respsOf (α ++ [.inv p o]) q = respsOf α q := by simp [respsOf_append]

/-- Internal steps do not change the responses of a process. -/
lemma respsOf_append_tau (α : List (Label P A)) (p q : P) :
    respsOf (α ++ [.tau p]) q = respsOf α q := by simp [respsOf_append]

/-- A response of `p` does not change the responses of another process. -/
lemma respsOf_append_ret_of_ne (α : List (Label P A)) {p q : P} (r : A.Resp) (h : q ≠ p) :
    respsOf (α ++ [.ret p r]) q = respsOf α q := by simp [respsOf_append, Ne.symm h]

/-- Internal steps do not change the operation of an instance. -/
@[simp] lemma opOf_append_tau (α : List (Label P A)) (p : P) (x : OpId P) :
    opOf (α ++ [.tau p]) x = opOf α x := by simp [opOf]

/-- Responses do not change the operation of an instance. -/
@[simp] lemma opOf_append_ret (α : List (Label P A)) (p : P) (r : A.Resp) (x : OpId P) :
    opOf (α ++ [.ret p r]) x = opOf α x := by simp [opOf]

/-- An operation known after appending `ℓ` was known before, or `ℓ` is its invocation. -/
lemma opOf_concat_cases {α : List (Label P A)} {ℓ : Label P A} {x : OpId P} {o : A.Op}
    (h : opOf (α ++ [ℓ]) x = some o) :
    opOf α x = some o ∨ (ℓ = .inv x.1 o ∧ x.2 = (opsOf α x.1).length) := by
  simp only [opOf, opsOf_concat] at h ⊢
  rcases lt_or_ge x.2 (opsOf α x.1).length with hlt | hge
  · left; rwa [List.getElem?_append_left hlt] at h
  · right
    rw [List.getElem?_append_right hge] at h
    cases hl : ℓ.invOf x.1 with
    | none => simp [hl] at h
    | some o' =>
      rw [hl] at h
      rcases List.getElem?_eq_some_iff.1 h with ⟨h1, h2⟩
      simp only [Option.toList_some, List.length_singleton, List.getElem_singleton] at h1 h2
      subst h2; exact ⟨Label.eq_inv_of_invOf_eq_some hl, by omega⟩

/-- A response known after appending `ℓ` was known before, or `ℓ` is this response. -/
lemma respOf_concat_cases {α : List (Label P A)} {ℓ : Label P A} {x : OpId P} {r : A.Resp}
    (h : respOf (α ++ [ℓ]) x = some r) :
    respOf α x = some r ∨ (ℓ = .ret x.1 r ∧ x.2 = (respsOf α x.1).length) := by
  simp only [respOf, respsOf_concat] at h ⊢
  rcases lt_or_ge x.2 (respsOf α x.1).length with hlt | hge
  · left; rwa [List.getElem?_append_left hlt] at h
  · right
    rw [List.getElem?_append_right hge] at h
    cases hl : ℓ.retOf x.1 with
    | none => simp [hl] at h
    | some r' =>
      rw [hl] at h
      rcases List.getElem?_eq_some_iff.1 h with ⟨h1, h2⟩
      simp only [Option.toList_some, List.length_singleton, List.getElem_singleton] at h1 h2
      subst h2; exact ⟨Label.eq_ret_of_retOf_eq_some hl, by omega⟩

/-- The response of an instance of another process does not change when `p` returns. -/
lemma respOf_append_ret_of_ne {α : List (Label P A)} {p : P} {r : A.Resp} {x : OpId P}
    (hx : x.1 ≠ p) : respOf (α ++ [.ret p r]) x = respOf α x :=
  respOf_concat_of_ne fun _ h => hx (Label.ret.inj h).1.symm

/-! ### Completed instances after appending one label -/

/-- After `p` returns, the completed instances are the old ones and the current one of `p`. -/
lemma completed_append_ret {α : List (Label P A)} {p : P} {r : A.Resp} (x : OpId P) :
    Completed (α ++ [.ret p r]) x ↔ Completed α x ∨ x = (p, (respsOf α p).length) := by
  obtain ⟨q, k⟩ := x
  simp only [Completed, respsOf_append, respsOf_cons, Label.retOf_ret, respsOf_nil,
    List.append_nil, List.length_append, Prod.mk.injEq]
  by_cases hq : p = q
  · subst hq; simp; omega
  · simp [hq, Ne.symm hq]

/-- A response of `p` does not complete an instance of another process. -/
lemma completed_append_ret_of_ne {α : List (Label P A)} {p : P} {r : A.Resp} {x : OpId P}
    (hx : x.1 ≠ p) : Completed (α ++ [.ret p r]) x ↔ Completed α x := by
  rw [completed_append_ret]
  exact ⟨fun h => h.resolve_right fun h => hx (by rw [h]), Or.inl⟩

/-- Appending a label that is not a response does not complete any instance. -/
lemma completed_append_of_not_ret {α : List (Label P A)} {ℓ : Label P A}
    (hℓ : ∀ p r, ℓ ≠ .ret p r) (x : OpId P) : Completed (α ++ [ℓ]) x ↔ Completed α x := by
  simp only [Completed, respsOf_concat_of_ne (hℓ x.1)]

/-! ### Real-time order after appending labels -/

/-- Real-time order after appending one label: it held before, or `a` has completed and `b` has
not been invoked after the label. -/
lemma precedes_concat {α : List (Label P A)} {ℓ : Label P A} {a b : OpId P}
    (h : Precedes (α ++ [ℓ]) a b) :
    Precedes α a b ∨ (Completed (α ++ [ℓ]) a ∧ ¬ Invoked (α ++ [ℓ]) b) := by
  obtain ⟨β, γ, hsplit, h1, h2⟩ := h
  induction γ using List.reverseRecOn with
  | nil => right; simp only [List.append_nil] at hsplit; subst hsplit; exact ⟨h1, h2⟩
  | append_singleton γ x _ =>
    left
    rw [← List.append_assoc] at hsplit
    exact ⟨β, γ, (List.append_inj' hsplit rfl).1, h1, h2⟩

/-- Appending a label that is not a response creates no real-time precedence. -/
lemma Precedes.of_concat_of_not_ret {α : List (Label P A)} {ℓ : Label P A} {a b : OpId P}
    (hℓ : ∀ q r, ℓ ≠ .ret q r) (h : Precedes (α ++ [ℓ]) a b) : Precedes α a b := by
  rcases precedes_concat h with h | ⟨h1, h2⟩
  · exact h
  · exact ⟨α, [], by simp, (completed_append_of_not_ret hℓ a).1 h1, fun h3 => h2 h3.mono⟩

/-- Real-time precedence towards an already invoked instance is not created by new labels. -/
lemma not_precedes_append {α β : List (Label P A)} {a b : OpId P} (hb : Invoked α b)
    (h : ¬ Precedes α a b) : ¬ Precedes (α ++ β) a b :=
  fun h' => h (h'.of_append_of_invoked hb)

/-! ### Restricting to one process -/

/-- Restricting an execution to the labels of `p` keeps the operations of `p`. -/
lemma opsOf_filter_proc (α : List (Label P A)) (p : P) :
    opsOf (α.filter (fun ℓ => decide (ℓ.proc = p))) p = opsOf α p := by
  induction α with
  | nil => rfl
  | cons ℓ α ih =>
    by_cases h : ℓ.proc = p
    · simp [h, ih]
    · simp [h, ih, Label.invOf_eq_none_of_proc_ne h]

/-- Restricting an execution to the labels of `p` keeps the responses of `p`. -/
lemma respsOf_filter_proc (α : List (Label P A)) (p : P) :
    respsOf (α.filter (fun ℓ => decide (ℓ.proc = p))) p = respsOf α p := by
  induction α with
  | nil => rfl
  | cons ℓ α ih =>
    by_cases h : ℓ.proc = p
    · simp [h, ih]
    · simp [h, ih, Label.retOf_eq_none_of_proc_ne h]

end Cslib.SharedMemory

/-! ### Counting invocations -/

namespace Cslib.SharedMemory

variable {P : Type} {A : ObjSpec}

namespace Label

/-- The label is an invocation. -/
def isInv : Label P A → Bool
  | .inv _ _ => true
  | _ => false

@[simp] lemma isInv_inv (p : P) (o : A.Op) : (inv p o : Label P A).isInv = true := rfl
@[simp] lemma isInv_ret (p : P) (r : A.Resp) : (ret p r : Label P A).isInv = false := rfl
@[simp] lemma isInv_tau (p : P) : (tau p : Label P A).isInv = false := rfl

end Label

/-- The number of invocations in an execution. -/
def invCount (α : List (Label P A)) : ℕ := α.countP Label.isInv

/-- The empty execution has no invocations. -/
@[simp] lemma invCount_nil : invCount ([] : List (Label P A)) = 0 := rfl

/-- Invocations of a concatenation. -/
@[simp] lemma invCount_append (α β : List (Label P A)) :
    invCount (α ++ β) = invCount α + invCount β := List.countP_append ..

/-- Invocations after prepending a label. -/
@[simp] lemma invCount_cons (ℓ : Label P A) (α : List (Label P A)) :
    invCount (ℓ :: α) = invCount α + if ℓ.isInv then 1 else 0 := by
  simp [invCount, List.countP_cons]

/-- The number of invocations is the sum over the processes of their numbers of invocations. -/
lemma invCount_eq_sum [Fintype P] [DecidableEq P] (α : List (Label P A)) :
    invCount α = ∑ p, (opsOf α p).length := by
  induction α with
  | nil => simp
  | cons ℓ α ih =>
    simp only [invCount_cons, ih, opsOf_cons, List.length_append, Finset.sum_add_distrib]
    cases ℓ with
    | inv q o =>
      have h1 : ∀ p, ((Label.inv q o : Label P A).invOf p).toList.length =
          if q = p then 1 else 0 := by
        intro p; simp only [Label.invOf_inv]; split_ifs <;> rfl
      simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Label.isInv_inv]; omega
    | ret q r => simp
    | tau q => simp

end Cslib.SharedMemory

/-! ### Well-formed histories, real-time order and invocation order -/

namespace Cslib.SharedMemory

open List

variable {P : Type} {A : ObjSpec} [DecidableEq P]

/-- In a well-formed history, every prefix has at most one more invocation than responses per
process, and at least as many. -/
lemma WellFormed.counts {α β γ : List (Label P A)} (hα : WellFormed α) (h : α = β ++ γ) (p : P) :
    (respsOf β p).length ≤ (opsOf β p).length ∧
      (opsOf β p).length ≤ (respsOf β p).length + 1 := by
  induction β using List.reverseRecOn generalizing γ with
  | nil => simp
  | append_singleton β ℓ ih =>
    have ih' := ih (γ := ℓ :: γ) (by simp [h])
    have hwf := hα β ℓ γ (by simp [h]) p
    simp only [opsOf_append, respsOf_append, opsOf_cons, respsOf_cons, opsOf_nil, respsOf_nil,
      List.append_nil, List.length_append]
    cases ℓ with
    | inv q o =>
      by_cases hq : q = p
      · subst hq; have := hwf.1 (by simp); simp; omega
      · simp [hq]; omega
    | ret q x =>
      by_cases hq : q = p
      · subst hq; have := hwf.2 (by simp); simp; omega
      · simp [hq]; omega
    | tau q => simp; omega

/-- In a well-formed history, every process has at most as many responses as invocations. -/
lemma WellFormed.resps_le_ops {α : List (Label P A)} (hα : WellFormed α) (p : P) :
    (respsOf α p).length ≤ (opsOf α p).length :=
  (hα.counts (γ := []) (by simp) p).1

/-- A completed operation has been invoked (well-formed histories). -/
lemma WellFormed.invoked_of_completed {α : List (Label P A)} (hα : WellFormed α) {x : OpId P}
    (h : Completed α x) : Invoked α x :=
  lt_of_lt_of_le h (hα.resps_le_ops x.1)

/-- Real-time order is transitive (well-formed histories). -/
lemma Precedes.trans {α : List (Label P A)} (hα : WellFormed α) {a b c : OpId P}
    (h₁ : Precedes α a b) (h₂ : Precedes α b c) : Precedes α a c := by
  obtain ⟨β₁, γ₁, e₁, ha, hb⟩ := h₁
  obtain ⟨β₂, γ₂, e₂, hb', hc⟩ := h₂
  have hb'' : Invoked β₂ b := (hα.counts e₂ b.1).1.trans_lt' hb'
  rcases List.prefix_or_prefix_of_prefix (l₃ := α) ⟨γ₁, e₁.symm⟩ ⟨γ₂, e₂.symm⟩ with hp | hp
  · obtain ⟨δ, rfl⟩ := hp
    exact ⟨_, γ₂, e₂, ha.mono, hc⟩
  · obtain ⟨δ, rfl⟩ := hp
    exact absurd hb''.mono hb

/-- If `b` is invoked in `α ++ γ` and `a` precedes `b` there, then `a` has completed... at the
latest when `b` is invoked; in particular, if `b` is not invoked in `α`, the response of `a` is
in `α ++ γ` before `b`'s invocation. Special case used most often: `γ = [ℓ]`. -/
lemma Precedes.completed_of_append_singleton {α : List (Label P A)} {ℓ : Label P A}
    {a b : OpId P} (h : Precedes (α ++ [ℓ]) a b) (hb : Invoked (α ++ [ℓ]) b) :
    Completed α a := by
  obtain ⟨β, γ', e, ha, hnb⟩ := h
  rcases List.prefix_or_prefix_of_prefix (l₃ := α ++ [ℓ]) ⟨γ', e.symm⟩ (List.prefix_append α [ℓ])
    with hp | hp
  · obtain ⟨δ, rfl⟩ := hp
    exact ha.mono
  · obtain ⟨δ, hδ⟩ := hp
    rcases δ with _ | ⟨x, δ⟩
    · simp only [append_nil] at hδ; subst hδ; exact ha
    · have : β = α ++ [ℓ] := by
        have hl := congrArg List.length e
        have hl2 := congrArg List.length hδ
        simp at hl hl2
        obtain ⟨γ'', rfl⟩ : ∃ γ'', γ' = γ'' := ⟨_, rfl⟩
        have : γ' = [] := by
          rw [← List.length_eq_zero_iff]; omega
        simpa [this] using e.symm
      subst this; exact absurd hb hnb

/-- Program order: an operation of `p` can only precede later operations of `p`. -/
lemma Precedes.lt_of_proc {α : List (Label P A)} (hα : WellFormed α) {p : P} {i j : ℕ}
    (h : Precedes α (p, i) (p, j)) : i < j := by
  obtain ⟨β, γ, e, hi, hj⟩ := h
  have := (hα.counts e p).1
  simp only [Completed, Invoked] at hi hj
  omega

/-- Instances invoked in `α` in invocation order, numbering the invocations of `p` from `c p`. -/
def invIdsFrom (c : P → ℕ) : List (Label P A) → List (OpId P)
  | [] => []
  | .inv p _ :: α => (p, c p) :: invIdsFrom (Function.update c p (c p + 1)) α
  | .ret _ _ :: α => invIdsFrom c α
  | .tau _ :: α => invIdsFrom c α

/-- Instances invoked in `α`, in invocation order. -/
def invIds (α : List (Label P A)) : List (OpId P) := invIdsFrom (fun _ => 0) α

/-- The instances listed by `invIdsFrom c α`. -/
lemma mem_invIdsFrom (c : P → ℕ) (α : List (Label P A)) (x : OpId P) :
    x ∈ invIdsFrom c α ↔ c x.1 ≤ x.2 ∧ x.2 < c x.1 + (opsOf α x.1).length := by
  induction α generalizing c with
  | nil => simp [invIdsFrom]
  | cons ℓ α ih =>
    cases ℓ with
    | inv p o =>
      simp only [invIdsFrom, mem_cons, ih, opsOf_cons, Label.invOf_inv, length_append]
      obtain ⟨q, k⟩ := x
      by_cases hq : p = q
      · subst hq; simp [Function.update_self]; omega
      · have hqp : q ≠ p := Ne.symm hq
        simp [hq, hqp]
    | ret p r => simp [invIdsFrom, ih]
    | tau p => simp [invIdsFrom, ih]

/-- `invIds α` lists exactly the invoked instances. -/
lemma mem_invIds (α : List (Label P A)) (x : OpId P) : x ∈ invIds α ↔ Invoked α x := by
  simp [invIds, mem_invIdsFrom, Invoked]

/-- `invIdsFrom c α` has no duplicates. -/
lemma nodup_invIdsFrom (c : P → ℕ) (α : List (Label P A)) : (invIdsFrom c α).Nodup := by
  induction α generalizing c with
  | nil => simp [invIdsFrom]
  | cons ℓ α ih =>
    cases ℓ with
    | inv p o =>
      simp only [invIdsFrom, nodup_cons, mem_invIdsFrom, Function.update_self]
      exact ⟨by omega, ih _⟩
    | ret p r => exact ih c
    | tau p => exact ih c

/-- `invIds α` has no duplicates. -/
lemma nodup_invIds (α : List (Label P A)) : (invIds α).Nodup := nodup_invIdsFrom _ _

/-- The invocation counters after `α`, starting from the counters `c`: `c p` plus the number of
invocations of `p` in `α`. -/
def invCountFrom (c : P → ℕ) (α : List (Label P A)) : P → ℕ := fun p => c p + (opsOf α p).length

/-- `invIdsFrom` of a concatenation. -/
lemma invIdsFrom_append (c : P → ℕ) (α β : List (Label P A)) :
    invIdsFrom c (α ++ β) = invIdsFrom c α ++ invIdsFrom (invCountFrom c α) β := by
  induction α generalizing c with
  | nil =>
    have : invCountFrom c ([] : List (Label P A)) = c := by funext p; simp [invCountFrom]
    simp [invIdsFrom, this]
  | cons ℓ α ih =>
    cases ℓ with
    | inv p o =>
      simp only [cons_append, invIdsFrom, ih, cons.injEq, true_and]
      congr 2
      funext q
      by_cases hq : q = p
      · subst hq; simp [invCountFrom, Function.update_self]; omega
      · simp [invCountFrom, Function.update_of_ne hq, Ne.symm hq]
    | ret p r => simp only [cons_append, invIdsFrom, ih]; rfl
    | tau p => simp only [cons_append, invIdsFrom, ih]; rfl

/-- Real-time order implies invocation order. -/
lemma Precedes.sublist_invIds {α : List (Label P A)} {a b : OpId P} (h : Precedes α a b)
    (hb : Invoked α b) (hwf : WellFormed α) : [a, b].Sublist (invIds α) := by
  obtain ⟨β, γ, rfl, ha, hnb⟩ := h
  have ha' : Invoked β a := lt_of_lt_of_le ha
    ((hwf.counts (γ := γ) rfl a.1).1)
  rw [invIds, invIdsFrom_append]
  refine (List.singleton_sublist.2 ((mem_invIds β a).2 ha')).append
    (List.singleton_sublist.2 ?_)
  rw [mem_invIdsFrom]
  simp only [Invoked, opsOf_append, length_append, invCountFrom, Nat.zero_add, not_lt] at hb hnb ⊢
  omega

/-- Extending a well-formed history by one label. -/
lemma WellFormed.append_singleton {α : List (Label P A)} {ℓ : Label P A} (hα : WellFormed α)
    (hℓ : ∀ p, (ℓ.invOf p ≠ none → (opsOf α p).length = (respsOf α p).length) ∧
      (ℓ.retOf p ≠ none → (opsOf α p).length = (respsOf α p).length + 1)) :
    WellFormed (α ++ [ℓ]) := by
  intro β ℓ' γ he q
  rcases List.eq_nil_or_concat' γ with rfl | ⟨γ', x, rfl⟩
  · obtain ⟨rfl, h2⟩ := List.append_inj' he.symm rfl
    simp only [List.cons.injEq, and_true] at h2
    subst h2
    exact hℓ q
  · have : α ++ [ℓ] = (β ++ ℓ' :: γ') ++ [x] := by rw [he]; simp
    obtain ⟨h1, -⟩ := List.append_inj' this rfl
    exact hα β ℓ' γ' h1 q

/-- Appending an invocation of a process without pending operation keeps a history well
formed. -/
lemma WellFormed.append_inv {α : List (Label P A)} {p : P} {o : A.Op} (hα : WellFormed α)
    (hp : (opsOf α p).length = (respsOf α p).length) : WellFormed (α ++ [.inv p o]) := by
  refine hα.append_singleton (fun q => ⟨fun h => ?_, fun h => by simp at h⟩)
  by_cases hq : p = q
  · subst hq; exact hp
  · simp [hq] at h

/-- Appending a response of a process with a pending operation keeps a history well formed. -/
lemma WellFormed.append_ret {α : List (Label P A)} {p : P} {r : A.Resp} (hα : WellFormed α)
    (hp : (opsOf α p).length = (respsOf α p).length + 1) : WellFormed (α ++ [.ret p r]) := by
  refine hα.append_singleton (fun q => ⟨fun h => by simp at h, fun h => ?_⟩)
  by_cases hq : p = q
  · subst hq; exact hp
  · simp [hq] at h

/-- Real-time order towards an operation invoked before an extension is unchanged. -/
lemma precedes_append_iff_of_invoked {α β : List (Label P A)} {a b : OpId P}
    (hb : Invoked α b) : Precedes (α ++ β) a b ↔ Precedes α a b :=
  ⟨fun h => h.of_append_of_invoked hb, Precedes.mono⟩

/-- The operations preceding a new invocation are exactly the completed ones. -/
lemma precedes_append_inv_iff {α : List (Label P A)} {p : P} {o : A.Op} {y : OpId P} :
    Precedes (α ++ [.inv p o]) y (p, (opsOf α p).length) ↔ Completed α y := by
  constructor
  · rintro ⟨β, γ, he, hc, hni⟩
    rcases List.prefix_or_prefix_of_prefix (l₃ := α ++ [.inv p o]) ⟨γ, he.symm⟩
      (List.prefix_append α [.inv p o]) with hp | hp
    · obtain ⟨δ, rfl⟩ := hp; exact hc.mono
    · obtain ⟨δ, rfl⟩ := hp
      rcases δ with _ | ⟨z, δ⟩
      · simpa using hc
      · simp only [append_assoc, cons_append, append_cancel_left_eq, cons.injEq, nil_eq,
          append_eq_nil_iff] at he
        obtain ⟨rfl, -, -⟩ := he
        exact absurd (by simp [Invoked]) hni
  · intro hc
    exact ⟨α, [.inv p o], rfl, hc, by simp [Invoked]⟩

/-- Once `b` is invoked while `a` is still pending, `a` never precedes `b`. -/
lemma Precedes.not_of_invoked {α β : List (Label P A)} {a b : OpId P} (hb : Invoked α b)
    (ha : ¬ Completed α a) : ¬ Precedes (α ++ β) a b := by
  rintro ⟨β₁, γ, hsplit, h1, h2⟩
  rcases List.append_eq_append_iff.1 hsplit with ⟨a', rfl, -⟩ | ⟨c', rfl, -⟩
  · exact h2 hb.mono
  · exact ha h1.mono

lemma completed_iff_respOf {α : List (Label P A)} {x : OpId P} :
    Completed α x ↔ (respOf α x).isSome := by
  simp [Completed, respOf]

/-- The responses after `p` returns `r`: the current instance of `p` gets the response `r`. -/
lemma respOf_append_ret (α : List (Label P A)) (p : P) (r : A.Resp) (y : OpId P) :
    respOf (α ++ [.ret p r]) y =
      if y = (p, (respsOf α p).length) then some r else respOf α y := by
  obtain ⟨q, k⟩ := y
  simp only [respOf, respsOf_append, respsOf_cons, Label.retOf_ret, respsOf_nil, append_nil,
    Prod.mk.injEq]
  by_cases hq : p = q
  · subst hq
    simp only [ite_true, Option.toList_some, true_and]
    rcases lt_trichotomy k (respsOf α p).length with h | rfl | h
    · rw [getElem?_append_left h, ite_eq_right (by omega)]
    · simp
    · rw [ite_eq_right (by omega), getElem?_eq_none (by simp; omega), getElem?_eq_none (by omega)]
  · simp [hq, Ne.symm hq]

end Cslib.SharedMemory
