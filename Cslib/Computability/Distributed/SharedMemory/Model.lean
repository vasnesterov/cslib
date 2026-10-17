/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.History

/-!
# The asynchronous shared-memory model

`n` processes (any type `P`) communicate through shared *base objects* `B i`, `i : ι`, each
given by a sequential specification (`ObjSpec`) and accessed atomically. An *implementation*
of a high-level object `A` from the base objects `B` specifies, for every process, a
deterministic program:

* `locInit p` — the initial local state of `p`,
* `invoke p l o` — the local state after `p` (in local state `l`) receives an invocation of `o`,
* `act p l` — what `p` does next in local state `l` while it has a pending operation: either
  apply primitive `o` to base object `i` and continue with `k (response)`
  (`Action.access i o k`), or return response `r` and continue in local state `l'`
  (`Action.ret r l'`),
* `memInit` — the initial state of the base objects,
* `allowed p o` — which high-level operations process `p` may invoke (e.g. single-writer /
  single-reader disciplines); executions only contain allowed invocations.

A configuration consists of the local states, the pending high-level operation of every
process and the states of all base objects (`mem`, the *memory representation*). Executions are
lists of labels (`Label P A`); since everything is deterministic, a finite execution is
determined by its labels, and `run α : Option Config` computes its final configuration
(`none` if `α` is not a valid execution).

Returning a response is a separate step of the process that does not access memory (as in I/O
automata); this is a harmless generalization of "the step that returns also accesses an object".

## Known limitations

* **Deterministic only**: processes and sequential specifications are deterministic; there are
  no nondeterministic programs, no randomization and no nondeterministic specifications.
* **No composition theorem**: a linearizable implementation cannot (yet) be substituted for an
  atomic base object with its properties inherited; clients have to be flattened by hand.
* **Base objects cannot see the caller**: process-dependent primitives (e.g. LL/SC contexts) must
  take the process identifier as an operation argument, which nothing enforces.
* `allowed` restricts which invocations appear in executions; every result must assume that the
  relevant operations are allowed for the relevant processes, otherwise it may be vacuous.
* `ObjSpec.init` of base objects is ignored (`memInit` is used instead).
* No crashes / crash recovery / `t`-resilience, no fairness predicates, no lock-based progress
  conditions (deadlock- or starvation-freedom) and no step complexity. `LockFree` is only
  meaningful for finitely many processes.
* No task framework (consensus, renaming, set agreement), no valency or covering arguments.

## Step and run API

* forward step equations `Impl.step_inv_eq_some`, `Impl.step_tau_eq_some`,
  `Impl.step_ret_eq_some` (complementing the inversion lemmas `step_inv`/`step_tau`/`step_ret`);
* `Impl.run_concat`, the induction principle `Impl.run_induction` over executions,
  `Impl.invariant_of_run` (invariants of reachable configurations), `Impl.Reachable.step`,
  `Impl.allowed_of_mem_opsOf` (every invoked operation is allowed);
* `Impl.pend_none_of_opsOf_nil`, `Impl.run_pend_curOp`: a pending operation is the current
  instance of its process, invoked and not completed;
* consequences of the counting invariant `Impl.run_counts`: `Impl.run_resps_le_ops`,
  `Impl.run_idle_counts`, `Impl.run_pend_counts` (an idle process has as many responses as
  invocations, a pending one has one more invocation), `Impl.not_invoked_curOp_of_idle`,
  `Impl.opsOf_ne_nil_of_pend`, `Impl.respsOf_ne_nil_of_idle`;
* `Impl.exists_linFun_of_run`, `Impl.linearizable_of_run`: choosing a linearization function from
  an invariant of the finite executions.

## Computable steps

`Impl.step` decides the invocation discipline `allowed` and the equality of responses
classically, so concrete executions cannot be evaluated with `decide`. Given decidability
instances, `Impl.cstep` is a computable copy of the step function (`Impl.step_eq_cstep`), and
`Impl.crunFrom` / `Impl.crun` the corresponding runs (`Impl.runFrom_eq_crunFrom`,
`Impl.run_eq_crun`, `Impl.valid_of_crun`).
-/

@[expose] public section

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

/-- What a process with a pending operation does next. -/
inductive Action (A : ObjSpec) (B : ι → ObjSpec) (L : Type) where
  /-- Apply primitive `o` to base object `i`, continue in local state `k r` where `r` is the
  primitive's response. -/
  | access (i : ι) (o : (B i).Op) (k : (B i).Resp → L)
  /-- Return response `r` of the high-level operation and continue in local state `l`. -/
  | ret (r : A.Resp) (l : L)

/-- An implementation of the high-level object `A` from base objects `B`, for processes `P`
with local states `L`. -/
structure Impl (A : ObjSpec) (B : ι → ObjSpec) (P L : Type) where
  /-- Initial states of the base objects. -/
  memInit : (i : ι) → (B i).State
  /-- Initial local states. -/
  locInit : P → L
  /-- Local state after receiving an invocation. -/
  invoke : P → L → A.Op → L
  /-- Next action of a process with a pending operation. -/
  act : P → L → Action A B L
  /-- Which operations a process may invoke. -/
  allowed : P → A.Op → Prop := fun _ _ => True

/-- A configuration of the system. -/
structure Config (A : ObjSpec) (B : ι → ObjSpec) (P L : Type) where
  /-- Local states. -/
  loc : P → L
  /-- Pending high-level operation of each process (`none` = idle). -/
  pend : P → Option A.Op
  /-- States of the base objects (the memory representation `mem(C)`). -/
  mem : (i : ι) → (B i).State

namespace Config

/-- No operation is pending (paper: quiescent). -/
def Quiescent (C : Config A B P L) : Prop := ∀ p, C.pend p = none

/-- No state-changing operation is pending (paper: state-quiescent). -/
def StateQuiescent (C : Config A B P L) : Prop := ∀ p o, C.pend p = some o → A.ReadOnly o

lemma Quiescent.stateQuiescent {C : Config A B P L} (h : C.Quiescent) : C.StateQuiescent := by
  intro p o hp; simp [h p] at hp

end Config

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-- The initial configuration. -/
def initCfg : Config A B P L := ⟨I.locInit, fun _ => none, I.memInit⟩

/-- The (deterministic) effect of a labelled step; `none` if the step is not enabled. -/
noncomputable def step (C : Config A B P L) : Label P A → Option (Config A B P L)
  | .inv p o => by
    classical
    exact if C.pend p = none ∧ I.allowed p o then
      some { C with pend := Function.update C.pend p (some o),
                    loc := Function.update C.loc p (I.invoke p (C.loc p) o) }
    else none
  | .tau p =>
    if C.pend p = none then none else
    match I.act p (C.loc p) with
    | .access i o k =>
      some { C with mem := Function.update C.mem i ((B i).δ (C.mem i) o).1,
                    loc := Function.update C.loc p (k ((B i).δ (C.mem i) o).2) }
    | .ret _ _ => none
  | .ret p r =>
    if C.pend p = none then none else
    match I.act p (C.loc p) with
    | .access _ _ _ => none
    | .ret r' l => by
      classical
      exact if r = r' then
        some { C with pend := Function.update C.pend p none, loc := Function.update C.loc p l }
      else none

/-- Run a list of labels from a configuration. -/
noncomputable def runFrom (C : Config A B P L) : List (Label P A) → Option (Config A B P L)
  | [] => some C
  | ℓ :: α => (I.step C ℓ).bind (fun C' => runFrom C' α)

/-- The final configuration of the execution `α` from the initial configuration. -/
noncomputable def run (α : List (Label P A)) : Option (Config A B P L) := I.runFrom I.initCfg α

/-- `α` is a (finite) execution of the implementation. -/
def Valid (α : List (Label P A)) : Prop := ∃ C, I.run α = some C

/-- `C` is reachable. -/
def Reachable (C : Config A B P L) : Prop := ∃ α, I.run α = some C

@[simp] lemma runFrom_nil (C : Config A B P L) : I.runFrom C [] = some C := rfl

@[simp] lemma runFrom_cons (C : Config A B P L) (ℓ : Label P A) (α : List (Label P A)) :
    I.runFrom C (ℓ :: α) = (I.step C ℓ).bind (fun C' => I.runFrom C' α) := rfl

lemma runFrom_append (C : Config A B P L) (α β : List (Label P A)) :
    I.runFrom C (α ++ β) = (I.runFrom C α).bind (fun C' => I.runFrom C' β) := by
  induction α generalizing C with
  | nil => simp
  | cons ℓ α ih =>
    simp only [List.cons_append, runFrom_cons, ih]
    cases I.step C ℓ <;> simp

lemma runFrom_append_of_eq {C C' : Config A B P L} {α : List (Label P A)}
    (h : I.runFrom C α = some C') (β : List (Label P A)) :
    I.runFrom C (α ++ β) = I.runFrom C' β := by
  rw [runFrom_append, h]; rfl

lemma run_append_of_eq {C : Config A B P L} {α : List (Label P A)}
    (h : I.run α = some C) (β : List (Label P A)) :
    I.run (α ++ β) = I.runFrom C β := I.runFrom_append_of_eq h β

lemma runFrom_singleton (C : Config A B P L) (ℓ : Label P A) :
    I.runFrom C [ℓ] = I.step C ℓ := by
  simp only [runFrom_cons, runFrom_nil]; cases I.step C ℓ <;> rfl

@[simp] lemma run_nil : I.run [] = some I.initCfg := rfl

lemma Valid.of_append {α β : List (Label P A)} (h : I.Valid (α ++ β)) : I.Valid α := by
  obtain ⟨C, hC⟩ := h
  rw [run, runFrom_append] at hC
  cases h' : I.runFrom I.initCfg α with
  | none => simp [h'] at hC
  | some C' => exact ⟨C', h'⟩

lemma valid_of_prefix {α β : List (Label P A)} (h : I.Valid β) (hp : α <+: β) : I.Valid α := by
  obtain ⟨γ, rfl⟩ := hp; exact h.of_append

/-! ### Effects of individual steps -/

section Steps

variable {I}

lemma step_inv {C C' : Config A B P L} {p : P} {o : A.Op}
    (h : I.step C (.inv p o) = some C') :
    C.pend p = none ∧ I.allowed p o ∧ C'.pend = Function.update C.pend p (some o) ∧
      C'.loc = Function.update C.loc p (I.invoke p (C.loc p) o) ∧ C'.mem = C.mem := by
  classical
  simp only [step] at h
  split_ifs at h with h1
  · cases h; exact ⟨h1.1, h1.2, rfl, rfl, rfl⟩

lemma step_tau {C C' : Config A B P L} {p : P} (h : I.step C (.tau p) = some C') :
    C.pend p ≠ none ∧ C'.pend = C.pend ∧ ∃ i o k, I.act p (C.loc p) = .access i o k ∧
      C'.mem = Function.update C.mem i ((B i).δ (C.mem i) o).1 ∧
      C'.loc = Function.update C.loc p (k ((B i).δ (C.mem i) o).2) := by
  simp only [step] at h
  split_ifs at h with h1
  refine ⟨h1, ?_⟩
  split at h
  · rename_i i o k hact
    cases h; exact ⟨rfl, i, o, k, hact, rfl, rfl⟩
  · cases h

lemma step_ret {C C' : Config A B P L} {p : P} {r : A.Resp}
    (h : I.step C (.ret p r) = some C') :
    C.pend p ≠ none ∧ C'.pend = Function.update C.pend p none ∧ C'.mem = C.mem ∧
      ∃ l, I.act p (C.loc p) = .ret r l ∧ C'.loc = Function.update C.loc p l := by
  classical
  simp only [step] at h
  split_ifs at h with h1
  refine ⟨h1, ?_⟩
  split at h
  · cases h
  · rename_i r' l hact
    split_ifs at h with h2
    cases h; subst h2; exact ⟨rfl, rfl, l, hact, rfl⟩

/-- A step of process `p` does not change the local state and pending operation of `q ≠ p`. -/
lemma step_other {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C')
    {q : P} (hq : ℓ.proc ≠ q) : C'.loc q = C.loc q ∧ C'.pend q = C.pend q := by
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, h1, h2, -⟩ := step_inv h
    simp only [Label.proc] at hq
    simp [h1, h2, Function.update_of_ne (Ne.symm hq)]
  | tau p =>
    obtain ⟨-, h1, i, o, k, -, -, h2⟩ := step_tau h
    simp only [Label.proc] at hq
    simp [h1, h2, Function.update_of_ne (Ne.symm hq)]
  | ret p r =>
    obtain ⟨-, h1, -, l, -, h2⟩ := step_ret h
    simp only [Label.proc] at hq
    simp [h1, h2, Function.update_of_ne (Ne.symm hq)]

lemma step_pend_some {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C')
    {p : P} {o : A.Op} (hp : C'.pend p = some o) :
    C.pend p = some o ∨ ℓ = .inv p o := by
  by_cases hq : ℓ.proc = p
  · cases ℓ with
    | inv p' o' =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, h1, -, -⟩ := step_inv h
      simp only [h1, Function.update_self, Option.some.injEq] at hp; exact Or.inr (by rw [hp])
    | tau p' =>
      obtain ⟨-, h1, -⟩ := step_tau h
      exact Or.inl (by rw [← hp, h1])
    | ret p' r =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, h1, -⟩ := step_ret h
      simp [h1] at hp
  · exact Or.inl (by rw [← hp, (step_other h hq).2])

end Steps

/-! ### Well-formedness and pending operations -/

/-- The counting invariant: in the configuration reached by a valid execution, process `p` has
invoked as many operations as it has returned, plus one if it has a pending operation, which is
its last invoked operation. -/
lemma runFrom_counts {C C' : Config A B P L} {α : List (Label P A)}
    (h : I.runFrom C α = some C') (p : P) (n m : ℕ)
    (hC : (C.pend p = none ∧ n = m) ∨ (C.pend p ≠ none ∧ n = m + 1)) :
    (C'.pend p = none ∧ n + (opsOf α p).length = m + (respsOf α p).length) ∨
    (C'.pend p ≠ none ∧ n + (opsOf α p).length = m + (respsOf α p).length + 1) := by
  induction α generalizing C n m with
  | nil => simp only [runFrom_nil, Option.some.injEq] at h; subst h; simpa using hC
  | cons ℓ α ih =>
    simp only [runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      have key := ih h (n + (ℓ.invOf p).toList.length) (m + (ℓ.retOf p).toList.length) ?_
      · simp only [opsOf_cons, respsOf_cons, List.length_append] at key ⊢
        rcases key with ⟨a, b⟩ | ⟨a, b⟩
        · left; exact ⟨a, by omega⟩
        · right; exact ⟨a, by omega⟩
      · by_cases hq : ℓ.proc = p
        · cases ℓ with
          | inv p' o =>
            simp only [Label.proc] at hq; subst hq
            obtain ⟨h0, -, h1, -⟩ := step_inv hs
            simp only [h0, true_and, ne_eq, not_true_eq_false, false_and, or_false] at hC
            right; simp [h1, hC]
          | tau p' =>
            simp only [Label.proc] at hq; subst hq
            obtain ⟨h0, h1, -⟩ := step_tau hs
            simp only [h0, false_and, ne_eq, not_false_eq_true, true_and, false_or] at hC
            right; simp [h1, h0, hC]
          | ret p' r =>
            simp only [Label.proc] at hq; subst hq
            obtain ⟨h0, h1, -⟩ := step_ret hs
            simp only [h0, false_and, ne_eq, not_false_eq_true, true_and, false_or] at hC
            left; simp [h1, hC]
        · rw [Label.invOf_eq_none_of_proc_ne hq, Label.retOf_eq_none_of_proc_ne hq,
            (step_other hs hq).2]
          simpa using hC

/-- Counting invariant for executions from the initial configuration. -/
lemma run_counts {C : Config A B P L} {α : List (Label P A)} (h : I.run α = some C) (p : P) :
    (C.pend p = none ∧ (opsOf α p).length = (respsOf α p).length) ∨
    (C.pend p ≠ none ∧ (opsOf α p).length = (respsOf α p).length + 1) := by
  have := I.runFrom_counts h p 0 0 (Or.inl ⟨rfl, rfl⟩)
  simpa using this

/-- Executions have well-formed histories. -/
lemma Valid.wellFormed {α : List (Label P A)} (h : I.Valid α) : WellFormed α := by
  intro β ℓ γ hα p
  obtain ⟨C, hC⟩ := h
  subst hα
  rw [run, runFrom_append] at hC
  cases hβ : I.runFrom I.initCfg β with
  | none => simp [hβ] at hC
  | some C₁ =>
    simp only [hβ, Option.bind_some, runFrom_cons] at hC
    cases hs : I.step C₁ ℓ with
    | none => simp [hs] at hC
    | some C₂ =>
      have hcnt := I.run_counts hβ p
      constructor
      · intro hi
        cases ℓ with
        | inv q o =>
          simp only [Label.invOf_inv, ne_eq, ite_eq_right_iff, reduceCtorEq, imp_false,
            not_not] at hi
          subst hi
          have := (step_inv hs).1
          rcases hcnt with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact h2
          · exact absurd this h1
        | ret q r => simp at hi
        | tau q => simp at hi
      · intro hi
        cases ℓ with
        | inv q o => simp at hi
        | tau q => simp at hi
        | ret q r =>
          simp only [Label.retOf_ret, ne_eq, ite_eq_right_iff, reduceCtorEq, imp_false,
            not_not] at hi
          subst hi
          have := (step_ret hs).1
          rcases hcnt with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact absurd h1 this
          · exact h2

/-- In a reachable configuration, a pending operation is the last invoked one. -/
lemma run_pend {C : Config A B P L} {α : List (Label P A)} (h : I.run α = some C) {p : P}
    {o : A.Op} (hp : C.pend p = some o) : (opsOf α p).getLast? = some o := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simp only [run, runFrom, initCfg, Option.some.injEq] at h; subst h; simp at hp
  | append_singleton α ℓ ih =>
    rw [run, runFrom_append] at h
    cases hα : I.runFrom I.initCfg α with
    | none => simp [hα] at h
    | some C₁ =>
      simp only [hα, Option.bind_some, runFrom_singleton] at h
      rcases step_pend_some h hp with h1 | h1
      · have := ih hα h1
        have hne : ℓ.invOf p = none := by
          cases ℓ with
          | inv q o' =>
            by_cases hq : q = p
            · subst hq; exact absurd h1 (by simp [(step_inv h).1])
            · simp [hq]
          | _ => rfl
        simp [opsOf_append, hne, this]
      · subst h1; simp [opsOf_append]

/-! ### Progress conditions -/

/-- An infinite execution. -/
structure InfExec where
  /-- Configurations. -/
  cfg : ℕ → Config A B P L
  /-- Labels. -/
  lbl : ℕ → Label P A
  cfg_zero : cfg 0 = I.initCfg
  step_eq : ∀ n, I.step (cfg n) (lbl n) = some (cfg (n + 1))

/-- Wait-freedom: in every infinite execution, a process whose operation stays pending forever
takes only finitely many steps (equivalently: every operation of a process that keeps taking
steps returns within finitely many of its own steps). -/
def WaitFree : Prop :=
  ∀ (e : I.InfExec) (p : P) (n : ℕ), (∀ m ≥ n, (e.cfg m).pend p ≠ none) →
    ∃ N, ∀ m ≥ N, e.lbl m ≠ .tau p

/-- Lock-freedom: every infinite execution with infinitely many steps (non-invocation labels)
has infinitely many responses. -/
def LockFree : Prop :=
  ∀ e : I.InfExec, (∀ N, ∃ m ≥ N, (e.lbl m).IsStep) → ∀ N, ∃ m ≥ N, ∃ p r, e.lbl m = .ret p r

/-- The next label of process `p` (meaningful when `p` has a pending operation). -/
def nextLabel (C : Config A B P L) (p : P) : Label P A :=
  match I.act p (C.loc p) with
  | .access _ _ _ => .tau p
  | .ret r _ => .ret p r

lemma step_nextLabel_isSome (C : Config A B P L) (p : P) (hp : C.pend p ≠ none) :
    (I.step C (I.nextLabel C p)).isSome := by
  unfold nextLabel
  split
  · rename_i i o k hact
    simp [step, hp, hact]
  · rename_i r l hact
    simp [step, hp, hact]

/-- One solo step of `p` (does nothing if `p` is idle). -/
noncomputable def soloStep (p : P) (C : Config A B P L) : Config A B P L :=
  if C.pend p = none then C else (I.step C (I.nextLabel C p)).getD C

/-- Labels of `k` solo steps of `p` from `C` (stopping early when `p` returns). -/
noncomputable def soloLabels (p : P) : Config A B P L → ℕ → List (Label P A)
  | _, 0 => []
  | C, k + 1 => if C.pend p = none then [] else I.nextLabel C p :: soloLabels p (I.soloStep p C) k

lemma runFrom_soloLabels (p : P) (C : Config A B P L) (k : ℕ) :
    I.runFrom C (I.soloLabels p C k) = some ((I.soloStep p)^[k] C) := by
  induction k generalizing C with
  | zero => rfl
  | succ k ih =>
    simp only [soloLabels, Function.iterate_succ, Function.comp_apply]
    by_cases hp : C.pend p = none
    · have hfix : ∀ j, (I.soloStep p)^[j] C = C := by
        intro j; induction j with
        | zero => rfl
        | succ j ihj => rw [Function.iterate_succ_apply', ihj]; simp [soloStep, hp]
      simp [hp, soloStep, hfix]
    · have hs := I.step_nextLabel_isSome C p hp
      obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 hs
      have : I.soloStep p C = C' := by simp [soloStep, hp, hC']
      simp only [hp, ↓reduceIte, runFrom_cons, hC', Option.bind_some, this]
      exact ih C'

/-- Obstruction-freedom: from every reachable configuration, a process with a pending operation
that runs solo returns within finitely many steps. -/
def ObstructionFree : Prop :=
  ∀ C p, I.Reachable C → C.pend p ≠ none → ∃ k, ((I.soloStep p)^[k] C).pend p = none

/-! ### Linearizability and history independence -/

/-- `h` is a linearization function: it maps every execution to a linearization of it. -/
def IsLinFun (h : List (Label P A) → List (OpId P × A.Op)) : Prop :=
  ∀ α, I.Valid α → IsLinearization α (h α)

/-- The implementation is linearizable. -/
def Linearizable : Prop := ∃ h, I.IsLinFun h

/-- History independence with respect to a set `E` of finite executions (Definition 4 of
Attiya et al., PODC 2024): for some linearization function `h`, any two executions in `E` whose
linearizations end in the same abstract state have the same memory representation. `E` may
depend on the execution and its final configuration. -/
def HIwrt (E : List (Label P A) → Config A B P L → Prop) : Prop :=
  ∃ h, I.IsLinFun h ∧ ∀ α α' C C', I.run α = some C → I.run α' = some C' → E α C → E α' C' →
    linState (h α) = linState (h α') → C.mem = C'.mem

/-- Perfect history independence (Definition 5): w.r.t. all finite executions. -/
def PerfectHI : Prop := I.HIwrt (fun _ _ => True)

/-- State-quiescent history independence (Definition 7). -/
def StateQuiescentHI : Prop := I.HIwrt (fun _ C => C.StateQuiescent)

/-- Quiescent history independence (Definition 8). -/
def QuiescentHI : Prop := I.HIwrt (fun _ C => C.Quiescent)

lemma HIwrt.mono {E E' : List (Label P A) → Config A B P L → Prop} (h : I.HIwrt E)
    (hE : ∀ α C, E' α C → E α C) : I.HIwrt E' := by
  obtain ⟨f, hf, hmem⟩ := h
  exact ⟨f, hf, fun α α' C C' h1 h2 h3 h4 h5 => hmem α α' C C' h1 h2 (hE _ _ h3) (hE _ _ h4) h5⟩

lemma PerfectHI.stateQuiescentHI (h : I.PerfectHI) : I.StateQuiescentHI :=
  HIwrt.mono I h (fun _ _ _ => trivial)

lemma StateQuiescentHI.quiescentHI (h : I.StateQuiescentHI) : I.QuiescentHI :=
  HIwrt.mono I h (fun _ _ hC => Config.Quiescent.stateQuiescent hC)

lemma HIwrt.linearizable {E : List (Label P A) → Config A B P L → Prop} (h : I.HIwrt E) :
    I.Linearizable := by
  obtain ⟨f, hf, -⟩ := h; exact ⟨f, hf⟩

end Impl

end Cslib.SharedMemory

/-! ## The step and run API -/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] {I : Impl A B P L}

/-! ### Forward step equations -/

lemma step_inv_eq_some {C : Config A B P L} {p : P} {o : A.Op} (h : C.pend p = none)
    (ho : I.allowed p o) :
    I.step C (.inv p o) =
      some { C with pend := Function.update C.pend p (some o),
                    loc := Function.update C.loc p (I.invoke p (C.loc p) o) } := by
  classical
  simp [step, h, ho]

lemma step_tau_eq_some {C : Config A B P L} {p : P} (h : C.pend p ≠ none) {i : ι}
    {o : (B i).Op} {k : (B i).Resp → L} (hact : I.act p (C.loc p) = .access i o k) :
    I.step C (.tau p) =
      some { C with mem := Function.update C.mem i ((B i).δ (C.mem i) o).1,
                    loc := Function.update C.loc p (k ((B i).δ (C.mem i) o).2) } := by
  simp [step, h, hact]

lemma step_ret_eq_some {C : Config A B P L} {p : P} (h : C.pend p ≠ none) {r : A.Resp} {l : L}
    (hact : I.act p (C.loc p) = .ret r l) :
    I.step C (.ret p r) =
      some { C with pend := Function.update C.pend p none,
                    loc := Function.update C.loc p l } := by
  classical
  simp [step, h, hact]

/-! ### Runs -/

variable (I) in
lemma run_concat (α : List (Label P A)) (ℓ : Label P A) :
    I.run (α ++ [ℓ]) = (I.run α).bind (fun C => I.step C ℓ) := by
  simp only [run, runFrom_append]
  cases I.runFrom I.initCfg α <;> simp

/-- Induction principle for properties of executions and their final configurations. -/
lemma run_induction {Q : List (Label P A) → Config A B P L → Prop} (h0 : Q [] I.initCfg)
    (hs : ∀ α C ℓ C', I.run α = some C → Q α C → I.step C ℓ = some C' → Q (α ++ [ℓ]) C')
    {α : List (Label P A)} {C : Config A B P L} (h : I.run α = some C) : Q α C := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simp only [run_nil, Option.some.injEq] at h; subst h; exact h0
  | append_singleton α ℓ ih =>
    rw [run_concat] at h
    cases hα : I.run α with
    | none => simp [hα] at h
    | some C₁ =>
      simp only [hα, Option.bind_some] at h
      exact hs α C₁ ℓ C hα (ih hα) h

/-- An invariant that holds initially and is preserved by all steps holds in every reachable
configuration. -/
lemma invariant_of_run {Inv : Config A B P L → Prop} (h0 : Inv I.initCfg)
    (hs : ∀ C ℓ C', Inv C → I.step C ℓ = some C' → Inv C') {α : List (Label P A)}
    {C : Config A B P L} (h : I.run α = some C) : Inv C :=
  run_induction (Q := fun _ C => Inv C) h0 (fun _ _ ℓ _ _ hC hs' => hs _ ℓ _ hC hs') h

variable (I) in
/-- Every operation invoked in an execution is allowed. -/
lemma allowed_of_mem_opsOf {α : List (Label P A)} (hα : I.Valid α) {p : P} {o : A.Op}
    (ho : o ∈ opsOf α p) : I.allowed p o := by
  obtain ⟨C, hC⟩ := hα
  refine I.run_induction (Q := fun α _ => ∀ o ∈ opsOf α p, I.allowed p o) (by simp)
    (fun α C ℓ C' _ ih hs o ho => ?_) hC o ho
  rw [opsOf_concat, List.mem_append] at ho
  rcases ho with ho | ho
  · exact ih o ho
  · cases ℓ with
    | inv q o' =>
      by_cases hq : q = p
      · subst hq
        simp only [Label.invOf_inv, ↓reduceIte, Option.toList_some, List.mem_singleton] at ho
        subst ho; exact (step_inv hs).2.1
      · simp [hq] at ho
    | ret q x => simp at ho
    | tau q => simp at ho

lemma Reachable.step {C C' : Config A B P L} (hC : I.Reachable C) {ℓ : Label P A}
    (h : I.step C ℓ = some C') : I.Reachable C' := by
  obtain ⟨α, hα⟩ := hC
  exact ⟨α ++ [ℓ], by rw [run_concat, hα, Option.bind_some, h]⟩

/-! ### Pending operations -/

/-- A process that has not invoked anything has no pending operation. -/
lemma pend_none_of_opsOf_nil {α : List (Label P A)} {C : Config A B P L}
    (h : I.run α = some C) {p : P} (hp : opsOf α p = []) : C.pend p = none := by
  rcases I.run_counts h p with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h1
  · rw [hp] at h2; simp at h2

/-- A pending operation is the current instance of its process: it has been invoked with this
operation and has not completed. -/
lemma run_pend_curOp {α : List (Label P A)} {C : Config A B P L} (h : I.run α = some C)
    {p : P} {o : A.Op} (hp : C.pend p = some o) :
    Invoked α (curOp α p) ∧ ¬ Completed α (curOp α p) ∧ opOf α (curOp α p) = some o := by
  have hlen : (opsOf α p).length = (respsOf α p).length + 1 := by
    rcases I.run_counts h p with ⟨h1, -⟩ | ⟨-, h2⟩
    · simp [h1] at hp
    · exact h2
  refine ⟨by simp [Invoked, hlen], by simp [Completed], ?_⟩
  have := I.run_pend h hp
  rw [List.getLast?_eq_getElem?] at this
  simpa [opOf, hlen] using this

section Idle

variable {α : List (Label P A)} {C : Config A B P L} {p : P}

/-- In an execution, a process has returned at most as often as it has invoked. -/
lemma run_resps_le_ops (h : I.run α = some C) (p : P) :
    (respsOf α p).length ≤ (opsOf α p).length := by
  rcases I.run_counts h p with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

/-- An idle process has as many responses as invocations. -/
lemma run_idle_counts (h : I.run α = some C) (hp : C.pend p = none) :
    (opsOf α p).length = (respsOf α p).length := by
  rcases I.run_counts h p with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2
  · exact absurd hp h1

/-- A pending process has one more invocation than responses. -/
lemma run_pend_counts (h : I.run α = some C) (hp : C.pend p ≠ none) :
    (opsOf α p).length = (respsOf α p).length + 1 := by
  rcases I.run_counts h p with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd h1 hp
  · exact h2

/-- The current instance of an idle process has not been invoked. -/
lemma not_invoked_curOp_of_idle (h : I.run α = some C) (hp : C.pend p = none) :
    ¬ Invoked α (curOp α p) := by
  simp [Invoked, I.run_idle_counts h hp]

/-- A pending process has invoked an operation. -/
lemma opsOf_ne_nil_of_pend (h : I.run α = some C) (hp : C.pend p ≠ none) : opsOf α p ≠ [] :=
  fun h0 => hp (I.pend_none_of_opsOf_nil h h0)

/-- An idle process that has invoked an operation has returned. -/
lemma respsOf_ne_nil_of_idle (h : I.run α = some C) (hp : C.pend p = none)
    (hops : opsOf α p ≠ []) : respsOf α p ≠ [] := by
  intro h0
  have := I.run_idle_counts h hp
  rw [h0] at this
  exact hops (List.eq_nil_of_length_eq_zero (by simpa using this))

end Idle

/-! ### Linearization functions from invariants -/

/-- If every finite execution has a witness `L` satisfying `Inv α C L`, then the witnesses can be
chosen by a function of the execution. -/
lemma exists_linFun_of_run {X : Type} [Inhabited X]
    {Inv : List (Label P A) → Config A B P L → X → Prop}
    (h : ∀ α C, I.run α = some C → ∃ L, Inv α C L) :
    ∃ f : List (Label P A) → X, ∀ α C, I.run α = some C → Inv α C (f α) := by
  classical
  refine ⟨fun α => if hα : ∃ C, I.run α = some C then (h α _ hα.choose_spec).choose else default,
    fun α C hC => ?_⟩
  suffices ∀ C' (hC' : I.run α = some C'), Inv α C (h α C' hC').choose by
    have hα : ∃ C, I.run α = some C := ⟨C, hC⟩
    simp only [hα, ↓reduceDIte]
    exact this _ hα.choose_spec
  intro C' hC'
  obtain rfl : C' = C := Option.some.inj (hC'.symm.trans hC)
  exact (h α C' hC').choose_spec

/-- An implementation all of whose finite executions have a linearization is linearizable. -/
theorem linearizable_of_run
    (h : ∀ α C, I.run α = some C → ∃ L : List (OpId P × A.Op), IsLinearization α L) :
    I.Linearizable := by
  obtain ⟨f, hf⟩ := exists_linFun_of_run (Inv := fun α _ L => IsLinearization α L) h
  exact ⟨f, fun α ⟨C, hC⟩ => hf α C hC⟩

end Impl

end Cslib.SharedMemory

/-! ## Computable steps -/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] [DecidableEq A.Resp] (I : Impl A B P L)
  [∀ p o, Decidable (I.allowed p o)]

/-- A computable copy of `Impl.step`. -/
def cstep (C : Config A B P L) : Label P A → Option (Config A B P L)
  | .inv p o =>
    if C.pend p = none ∧ I.allowed p o then
      some { C with pend := Function.update C.pend p (some o),
                    loc := Function.update C.loc p (I.invoke p (C.loc p) o) }
    else none
  | .tau p =>
    if C.pend p = none then none else
    match I.act p (C.loc p) with
    | .access i o k =>
      some { C with mem := Function.update C.mem i ((B i).δ (C.mem i) o).1,
                    loc := Function.update C.loc p (k ((B i).δ (C.mem i) o).2) }
    | .ret _ _ => none
  | .ret p r =>
    if C.pend p = none then none else
    match I.act p (C.loc p) with
    | .access _ _ _ => none
    | .ret r' l =>
      if r = r' then
        some { C with pend := Function.update C.pend p none, loc := Function.update C.loc p l }
      else none

lemma step_eq_cstep (C : Config A B P L) (ℓ : Label P A) : I.step C ℓ = I.cstep C ℓ := by
  cases ℓ with
  | inv p o => simp only [step, cstep]; congr 1
  | tau p => rfl
  | ret p r =>
    simp only [step, cstep]
    split_ifs
    · rfl
    · generalize I.act p (C.loc p) = a
      cases a with
      | access i o k => rfl
      | ret r' l => simp only; congr 1

/-- `Impl.runFrom` with `cstep`. -/
def crunFrom (C : Config A B P L) : List (Label P A) → Option (Config A B P L)
  | [] => some C
  | ℓ :: α => (I.cstep C ℓ).bind fun C' => crunFrom C' α

/-- `Impl.run` with `cstep`. -/
def crun (α : List (Label P A)) : Option (Config A B P L) := I.crunFrom I.initCfg α

lemma runFrom_eq_crunFrom (C : Config A B P L) (α : List (Label P A)) :
    I.runFrom C α = I.crunFrom C α := by
  induction α generalizing C with
  | nil => rfl
  | cons ℓ α ih => simp only [runFrom_cons, crunFrom, step_eq_cstep, ih]

lemma run_eq_crun (α : List (Label P A)) : I.run α = I.crun α :=
  I.runFrom_eq_crunFrom _ α

lemma valid_of_crun {α : List (Label P A)} (h : (I.crun α).isSome = true) : I.Valid α := by
  rw [Valid, run_eq_crun]
  exact Option.isSome_iff_exists.1 h

end Impl

end Cslib.SharedMemory
