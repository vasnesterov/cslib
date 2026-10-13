/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Mutex
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Action.Pi

/-!
# Memory-anonymous shared memory and symmetric algorithms

Model of Taubenfeld (PODC 2017) and Aghazadeh–Imbs–Raynal–Taubenfeld–Woelfel (PODC 2019).

* **Memory**: `m` registers with values in `V`, all initialized to the same value `bot`. A
  primitive step is either an arbitrary atomic *read-modify-write* `rmw x f` (replace the value
  `v` of register `x` by `f v`, return `v`; reads, writes, compare&swap are special cases) or an
  atomic *snapshot* of all registers. The whole memory is one CSLib base object (`memObj`).
* **Memory anonymity**: every process `p` has its own private permutation `π p` of the register
  names chosen by an adversary; when `p` uses the local name `x` it accesses the physical
  register `π p x` (and its snapshot is `fun x => mem (π p x)`).
* **Symmetric algorithms** (`SymAlg`): all processes run the same code; a process only differs
  by its identifier `a : Id` (initial local state `init a`). *Symmetry with equality* (identifiers
  can be stored, read and compared for equality only) is expressed semantically: the
  identifier group `Equiv.Perm Id` acts on register values and local states, and initial
  states, invocations and steps are equivariant (`SymAlg.Symmetric`); `bot` is not an
  identifier (it is fixed by every renaming).
* `SymAlg.impl A ids π`: the CSLib implementation run by processes `P` with identifiers
  `ids : P → Id` and anonymity permutations `π`.
* `SymAlg.ReadWrite`: the algorithm only uses reads, writes and snapshots (no other RMW).

High-level operations and responses are assumed not to involve identifiers (true for
`mutexObj`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

/-- Physical primitive operations on an array of `m` registers. -/
inductive AnonOp (m : ℕ) (V : Type)
  /-- Atomically replace the value `v` of register `x` by `f v` (returns `v`). -/
  | rmw (x : Fin m) (f : V → V)
  /-- Atomic snapshot of all registers. -/
  | snap

/-- The memory as a single base object. The response of every primitive is the memory before
the step (a `rmw` continuation only looks at the accessed register). -/
abbrev memObj (m : ℕ) (V : Type) (bot : V) : ObjSpec where
  State := Fin m → V
  Op := AnonOp m V
  Resp := Fin m → V
  init := fun _ => bot
  δ s o := match o with
    | .rmw x f => (Function.update s x (f (s x)), s)
    | .snap => (s, s)

/-- What a process does next, in terms of *local* register names. -/
inductive SymAction (m : ℕ) (V S R : Type)
  /-- Atomic read-modify-write of the local register `x`: new value `f v`, continue with `k v`
  where `v` is the old value. -/
  | rmw (x : Fin m) (f : V → V) (k : V → S)
  /-- Atomic snapshot (in local names), continue with `k view`. -/
  | snap (k : (Fin m → V) → S)
  /-- Return response `r` of the pending high-level operation, continue in local state `s`. -/
  | ret (r : R) (s : S)

/-- A symmetric algorithm for the high-level object `O` using `m` anonymous registers with
values in `V`, local states `S`, identifiers `Id`. -/
structure SymAlg (O : ObjSpec) (Id : Type) (m : ℕ) (V S : Type) where
  /-- Common initial value of all registers. -/
  bot : V
  /-- Initial local state of the process with identifier `a`. -/
  init : Id → S
  /-- Local state after an invocation. -/
  invoke : S → O.Op → S
  /-- Next action of a process with a pending operation. -/
  act : S → SymAction m V S O.Resp

namespace SymAction

variable {m : ℕ} {V S R G : Type} [Group G] [MulAction G V] [MulAction G S]

/-- Renaming an action by `σ` (conjugating its functions). -/
def smul (σ : G) : SymAction m V S R → SymAction m V S R
  | .rmw x f k => .rmw x (fun v => σ • f (σ⁻¹ • v)) (fun v => σ • k (σ⁻¹ • v))
  | .snap k => .snap (fun w => σ • k (σ⁻¹ • w))
  | .ret r s => .ret r (σ • s)

end SymAction

/-- Identifier renamings act on optional identifiers (`none` plays the role of `⊥`). -/
instance permOptionAction (Id : Type) : MulAction (Equiv.Perm Id) (Option Id) where
  smul σ o := o.map σ
  one_smul o := by cases o <;> rfl
  mul_smul σ τ o := by cases o <;> rfl

@[simp] lemma perm_smul_option {Id : Type} (σ : Equiv.Perm Id) (o : Option Id) :
    σ • o = o.map σ := rfl

namespace SymAlg

variable {O : ObjSpec} {Id : Type} {m : ℕ} {V S : Type}

/-- *Symmetry with equality*: everything is equivariant under renamings of identifiers, and the
initial register value is not an identifier. -/
structure Symmetric [MulAction (Equiv.Perm Id) V] [MulAction (Equiv.Perm Id) S]
    (A : SymAlg O Id m V S) : Prop where
  bot : ∀ σ : Equiv.Perm Id, σ • A.bot = A.bot
  init : ∀ (σ : Equiv.Perm Id) a, A.init (σ a) = σ • A.init a
  invoke : ∀ (σ : Equiv.Perm Id) s o, A.invoke (σ • s) o = σ • A.invoke s o
  act : ∀ (σ : Equiv.Perm Id) s, A.act (σ • s) = (A.act s).smul σ

/-- The algorithm only uses atomic reads, writes and snapshots: every `rmw` is a read
(`f = id`) or a write (constant `f`, continuation ignoring the old value). -/
def ReadWrite (A : SymAlg O Id m V S) : Prop :=
  ∀ s x f k, A.act s = .rmw x f k →
    (∀ v, f v = v) ∨ ∃ w s', (∀ v, f v = w) ∧ ∀ v, k v = s'

/-- The algorithm never takes snapshots (it only uses read-modify-write accesses of single
registers). -/
def NoSnapshot (A : SymAlg O Id m V S) : Prop := ∀ s k, A.act s ≠ .snap k

variable {P : Type}

/-- The implementation run by processes `P` with identifiers `ids` and anonymity permutations
`π` (process `p` accesses physical register `π p x` when it uses the local name `x`). -/
def impl (A : SymAlg O Id m V S) (ids : P → Id) (π : P → Equiv.Perm (Fin m)) :
    Impl O (fun _ : Unit => memObj m V A.bot) P S where
  memInit _ := fun _ => A.bot
  locInit p := A.init (ids p)
  invoke _ l o := A.invoke l o
  act p l := match A.act l with
    | .rmw x f k => .access () (.rmw (π p x) f) (fun r => k (r (π p x)))
    | .snap k => .access () .snap (fun r => k (fun x => r (π p x)))
    | .ret r s => .ret r s

end SymAlg

end Cslib.SharedMemory

namespace Cslib.SharedMemory.SymAlg

/-! ### Steps of `SymAlg.impl` -/

variable {O : ObjSpec} {Id : Type} {m : ℕ} {V S : Type} {P : Type} [DecidableEq P]
  (A : SymAlg O Id m V S) (ids : P → Id) (π : P → Equiv.Perm (Fin m))

/-- Configurations of `A.impl`. -/
abbrev Cfg := Config O (fun _ : Unit => memObj m V A.bot) P S

variable {A}

lemma impl_step_tau_rmw {C : A.Cfg} {p : P} {x : Fin m} {f : V → V} {k : V → S}
    (hp : C.pend p ≠ none) (hact : A.act (C.loc p) = .rmw x f k) :
    (A.impl ids π).step C (.tau p) = some { C with
      mem := Function.update C.mem () (Function.update (C.mem ()) (π p x) (f (C.mem () (π p x))))
      loc := Function.update C.loc p (k (C.mem () (π p x))) } := by
  simp only [Impl.step, hp, ite_false]
  simp only [impl, hact]

lemma impl_step_tau_snap {C : A.Cfg} {p : P} {k : (Fin m → V) → S}
    (hp : C.pend p ≠ none) (hact : A.act (C.loc p) = .snap k) :
    (A.impl ids π).step C (.tau p) = some { C with
      mem := Function.update C.mem () (C.mem ())
      loc := Function.update C.loc p (k (fun x => C.mem () (π p x))) } := by
  simp only [Impl.step, hp, ite_false]
  simp only [impl, hact]

lemma impl_step_ret {C : A.Cfg} {p : P} {r : O.Resp} {s : S}
    (hp : C.pend p ≠ none) (hact : A.act (C.loc p) = .ret r s) :
    (A.impl ids π).step C (.ret p r) = some { C with
      pend := Function.update C.pend p none
      loc := Function.update C.loc p s } := by
  simp only [Impl.step, hp, ite_false]
  simp only [impl, hact]
  simp

lemma impl_step_inv {C : A.Cfg} {p : P} {o : O.Op} (hp : C.pend p = none) :
    (A.impl ids π).step C (.inv p o) = some { C with
      pend := Function.update C.pend p (some o)
      loc := Function.update C.loc p (A.invoke (C.loc p) o) } := by
  simp [Impl.step, hp, impl]

end Cslib.SharedMemory.SymAlg

namespace Cslib.SharedMemory.SymAlg

variable {O : ObjSpec} {Id : Type} {m : ℕ} {V S : Type} {P : Type} [DecidableEq P]
  {A : SymAlg O Id m V S} {ids : P → Id} {π : P → Equiv.Perm (Fin m)}

/-- Inversion of an internal step of `A.impl`. -/
lemma impl_step_tau_cases {C C' : A.Cfg} {p : P} (h : (A.impl ids π).step C (.tau p) = some C') :
    C.pend p ≠ none ∧
    ((∃ x f k, A.act (C.loc p) = .rmw x f k ∧ C' = { C with
      mem := Function.update C.mem () (Function.update (C.mem ()) (π p x) (f (C.mem () (π p x))))
      loc := Function.update C.loc p (k (C.mem () (π p x))) }) ∨
     (∃ k, A.act (C.loc p) = .snap k ∧ C' = { C with
      mem := Function.update C.mem () (C.mem ())
      loc := Function.update C.loc p (k (fun x => C.mem () (π p x))) })) := by
  have hp : C.pend p ≠ none := by
    intro hn; simp [Impl.step, hn] at h
  refine ⟨hp, ?_⟩
  cases hact : A.act (C.loc p) with
  | rmw x f k =>
    rw [impl_step_tau_rmw ids π hp hact] at h
    exact Or.inl ⟨x, f, k, rfl, (Option.some.inj h).symm⟩
  | snap k =>
    rw [impl_step_tau_snap ids π hp hact] at h
    exact Or.inr ⟨k, rfl, (Option.some.inj h).symm⟩
  | ret r s =>
    simp [Impl.step, hp, impl, hact] at h

/-- Inversion of a response step of `A.impl`. -/
lemma impl_step_ret_cases {C C' : A.Cfg} {p : P} {r : O.Resp}
    (h : (A.impl ids π).step C (.ret p r) = some C') :
    C.pend p ≠ none ∧ ∃ s, A.act (C.loc p) = .ret r s ∧ C' = { C with
      pend := Function.update C.pend p none
      loc := Function.update C.loc p s } := by
  obtain ⟨hp, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  refine ⟨hp, l, ?_, ?_⟩
  · simp only [impl] at hact
    split at hact <;> simp_all
  · cases C'; simp_all

/-- Inversion of an invocation step of `A.impl`. -/
lemma impl_step_inv_cases {C C' : A.Cfg} {p : P} {o : O.Op}
    (h : (A.impl ids π).step C (.inv p o) = some C') :
    C.pend p = none ∧ C' = { C with
      pend := Function.update C.pend p (some o)
      loc := Function.update C.loc p (A.invoke (C.loc p) o) } := by
  obtain ⟨hp, -, hpend, hloc, hmem⟩ := Impl.step_inv h
  refine ⟨hp, ?_⟩
  cases C'; simp_all; rfl

end Cslib.SharedMemory.SymAlg
