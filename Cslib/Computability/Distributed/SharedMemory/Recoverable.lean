/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Spec
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Ring.Nat

/-!
# Asynchronous shared memory with crash-recovery (individual crashes)

A self-contained model of the standard crash-recovery shared-memory model with *individual*
crashes (Golab, SPAA'20; Delporte-Gallet–Fatourou–Fauconnier–Ruppert, PODC'22; Ovens, PODC'24):

* `n` deterministic processes `Fin n`; process `p` starts in the local state `A.init p x`
  determined by its input `x : Bool` (binary consensus: processes start with their inputs);
* shared objects indexed by `ι`, object `i` has a deterministic sequential specification
  `T i : ObjSpec` (CSLib); the algorithm fixes their initial values `A.mem₀`
  (`ObjSpec.init` is ignored);
* a local state either *outputs* a value (`Act.out v`, an output state; a step taken in an
  output state is a no-op) or is *poised* to apply operation `o` to object `i` and continue with
  `k r` on response `r` (`Act.access i o k`). Every step that is not a no-op is exactly one
  operation on one object (local computation is folded into the continuation);
* events: `Ev.step p` (the next step of `p`) and `Ev.crash p`. A crash **resets the local
  state of `p` (including its program counter) to its initial state** `A.init p (input p)`;
  **shared objects are unaffected** (non-volatile memory). Recovery = continuing from the
  initial state after a crash;
* the system is deterministic, so a finite execution from a configuration is its list of events
  (`run C α`) — executions from different configurations with the same schedule are the same list.

Correctness (`Solves A Adm`), relative to a set `Adm` of admissible event sequences:
* **agreement**: in every admissible finite execution from an initial configuration all output
  values (of all processes, also of different incarnations of one process) are equal;
* **validity**: every output value is the input of some process;
* **progress**: in every infinite execution all of whose prefixes are admissible, a process that
  takes infinitely many steps and does not crash after time `N` is in an output state at some
  time `≥ N` (i.e. it outputs in its last incarnation: "every process either crashes or outputs a
  value after taking a finite number of steps from its initial state").

`RecConsensus A := Solves A (fun _ => True)` is *recoverable wait-free consensus* (all crash
patterns allowed; progress = recoverable wait-freedom). `WFConsensus A := Solves A CrashFree` is
ordinary *wait-free consensus* (no crashes; a crashed process of the crash-stop model is one that
stops taking steps).

We also define Ovens' sets of executions with bounded crashes (`InE z`, `InEs z`: the number of
crashes of `p` is at most `z n` times the number of steps of processes with smaller identifiers —
in every prefix for `InEs`), indistinguishability, solo runs, valency, and prove the generic
valency lemmas of Ovens (PODC'24): Observation 1 (`biv_initial`), Lemma 6 (`exists_crit`,
`exists_stuck`), Lemma 7 (`Crit.teams`), Lemma 8 (`Crit.biv`), Lemma 9 (`Crit.poised`),
Observation 5
(`UnivQ.transfer`).

Finally, tools for algorithms in this model (also used as the crash-stop model, through
`WFConsensus`):

* `withRW R S`: the objects of an algorithm that uses read/write objects `R j` (in
  consensus-number statements `∀ j, (R j).RWLike`, see `ObjSpec.RWLike`) and objects of one
  type `S`;
* `objOf C p`, `accCount C α p i`: the object process `p` is poised to access, and the number of
  operations `p` applies to object `i` along `α` (`accCount_append`, `accCount_single`);
* `Cfg.Out.run`, `Dec.exists_out`: outputs persist along executions without crashes of the
  deciding process; `inv_run_crashFree`: invariants preserved by steps hold along crash-free
  executions; `pre_crashFree_iff`: an infinite execution is crash-free iff none of its events is
  a crash;
* `prog_of_rank`: progress — and thus (recoverable) wait-freedom — from a ranking of local states
  that decreases at every access; `wfConsensus_of_inv`: wait-free consensus from an invariant
  (all outputs are the input of one process) and a ranking function.
-/

@[expose] public section

namespace Cslib.SharedMemory.Recoverable

open Cslib.SharedMemory

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ}

/-- What a process does in a local state: apply operation `o` to object `i` and continue with
`k r` (where `r` is the response), or output `v` (an output state). -/
inductive Act (T : ι → ObjSpec) (L : Type) where
  /-- Apply `o` to object `i` and continue with `k r` on response `r`. -/
  | access (i : ι) (o : (T i).Op) (k : (T i).Resp → L)
  /-- Output `v`. -/
  | out (v : Bool)

/-- A (binary consensus) algorithm for `n` processes using objects `T i`, `i : ι`. -/
structure Alg (n : ℕ) (T : ι → ObjSpec) where
  /-- Local states. -/
  L : Type
  /-- Initial state of process `p` with input `x` (also the state after a crash). -/
  init : Fin n → Bool → L
  /-- The next action in a local state. -/
  act : L → Act T L
  /-- Initial values of the objects. -/
  mem₀ : (i : ι) → (T i).State

/-- Events: a step of a process or a crash of a process. -/
inductive Ev (n : ℕ) where
  /-- The next step of `p`. -/
  | step (p : Fin n)
  /-- A crash of `p` (followed by recovery from its initial state). -/
  | crash (p : Fin n)
  deriving DecidableEq

/-- The process of an event. -/
def Ev.proc : Ev n → Fin n
  | .step p => p
  | .crash p => p

@[simp] lemma Ev.proc_step (p : Fin n) : (Ev.step p).proc = p := rfl
@[simp] lemma Ev.proc_crash (p : Fin n) : (Ev.crash p).proc = p := rfl

variable (A : Alg n T)

/-- Configurations: inputs (fixed; they determine the state after a crash), local states,
object values. -/
structure Cfg where
  /-- The inputs of the processes (fixed; they determine the state after a crash). -/
  inp : Fin n → Bool
  /-- The local states of the processes. -/
  loc : Fin n → A.L
  /-- The values of the shared objects. -/
  mem : (i : ι) → (T i).State

variable {A}

/-- `p` is in an output state with value `v`. -/
def Cfg.Out (C : Cfg A) (p : Fin n) (v : Bool) : Prop := A.act (C.loc p) = .out v

/-- `p` is poised to apply an operation to object `i`. -/
def Cfg.Poised (C : Cfg A) (p : Fin n) (i : ι) : Prop :=
  ∃ o k, A.act (C.loc p) = .access i o k

/-- The next step of `p`. -/
def Cfg.stepP (C : Cfg A) (p : Fin n) : Cfg A :=
  match A.act (C.loc p) with
  | .access i o k =>
    { C with loc := Function.update C.loc p (k ((T i).δ (C.mem i) o).2)
             mem := Function.update C.mem i ((T i).δ (C.mem i) o).1 }
  | .out _ => C

/-- Apply an event. -/
def Cfg.next (C : Cfg A) : Ev n → Cfg A
  | .step p => C.stepP p
  | .crash p => { C with loc := Function.update C.loc p (A.init p (C.inp p)) }

/-- The configuration reached from `C` by the events `α`. -/
def run (C : Cfg A) (α : List (Ev n)) : Cfg A := α.foldl Cfg.next C

variable (A) in
/-- The initial configuration with inputs `x`. -/
def initCfg (x : Fin n → Bool) : Cfg A := ⟨x, fun p => A.init p (x p), A.mem₀⟩

@[simp] lemma run_nil (C : Cfg A) : run C [] = C := rfl

@[simp] lemma run_cons (C : Cfg A) (e : Ev n) (α : List (Ev n)) :
    run C (e :: α) = run (C.next e) α := rfl

lemma run_append (C : Cfg A) (α β : List (Ev n)) : run C (α ++ β) = run (run C α) β := by
  simp [run, List.foldl_append]

lemma run_concat (C : Cfg A) (α : List (Ev n)) (e : Ev n) :
    run C (α ++ [e]) = (run C α).next e := by
  simp [run_append]

@[simp] lemma next_inp (C : Cfg A) (e : Ev n) : (C.next e).inp = C.inp := by
  cases e with
  | step p =>
    simp only [Cfg.next, Cfg.stepP]
    split <;> rfl
  | crash p => rfl

@[simp] lemma run_inp (C : Cfg A) (α : List (Ev n)) : (run C α).inp = C.inp := by
  induction α generalizing C with
  | nil => rfl
  | cons e α ih => simp [ih]

lemma stepP_loc_other (C : Cfg A) {p q : Fin n} (h : q ≠ p) : (C.stepP p).loc q = C.loc q := by
  simp only [Cfg.stepP]
  split
  · simp [Function.update_of_ne h]
  · rfl

lemma next_loc_other (C : Cfg A) (e : Ev n) {q : Fin n} (h : q ≠ e.proc) :
    (C.next e).loc q = C.loc q := by
  cases e with
  | step p => exact stepP_loc_other C h
  | crash p => simp only [Cfg.next]; exact Function.update_of_ne (by simpa using h) _ _

/-- Events of other processes do not change the local state of `q`. -/
lemma run_loc_other (C : Cfg A) (α : List (Ev n)) {q : Fin n} (h : ∀ e ∈ α, e.proc ≠ q) :
    (run C α).loc q = C.loc q := by
  induction α generalizing C with
  | nil => rfl
  | cons e α ih =>
    simp only [run_cons]
    rw [ih _ (fun e' he' => h e' (by simp [he'])), next_loc_other C e (Ne.symm (h e (by simp)))]

@[simp] lemma crash_loc_self (C : Cfg A) (p : Fin n) :
    (C.next (.crash p)).loc p = A.init p (C.inp p) := by
  simp [Cfg.next]

@[simp] lemma crash_mem (C : Cfg A) (p : Fin n) : (C.next (.crash p)).mem = C.mem := rfl

lemma stepP_of_out (C : Cfg A) {p : Fin n} {v : Bool} (h : C.Out p v) : C.stepP p = C := by
  simp only [Cfg.stepP]
  rw [Cfg.Out] at h
  split <;> simp_all

lemma stepP_of_access (C : Cfg A) {p : Fin n} {i : ι} {o : (T i).Op} {k : (T i).Resp → A.L}
    (h : A.act (C.loc p) = .access i o k) :
    C.stepP p = { C with loc := Function.update C.loc p (k ((T i).δ (C.mem i) o).2)
                         mem := Function.update C.mem i ((T i).δ (C.mem i) o).1 } := by
  simp only [Cfg.stepP]
  split
  · rename_i i' o' k' h'
    rw [h] at h'
    cases h'
    rfl
  · rename_i h'
    rw [h] at h'
    cases h'

/-! ## Decisions -/

/-- Some process is in an output state with value `v` at some configuration of the execution
`α` from `C` (including `C` itself): "some process has decided `v` in `Cα`". -/
def Dec (C : Cfg A) (α : List (Ev n)) (v : Bool) : Prop :=
  ∃ k ≤ α.length, ∃ p, (run C (α.take k)).Out p v

lemma Dec.append_right {C : Cfg A} {α : List (Ev n)} {v : Bool} (h : Dec C α v)
    (β : List (Ev n)) : Dec C (α ++ β) v := by
  obtain ⟨k, hk, p, hp⟩ := h
  refine ⟨k, by simp; omega, p, ?_⟩
  rwa [List.take_append_of_le_length hk]

lemma Dec.of_suffix {C : Cfg A} {α β : List (Ev n)} {v : Bool} (h : Dec (run C α) β v) :
    Dec C (α ++ β) v := by
  obtain ⟨k, hk, p, hp⟩ := h
  refine ⟨α.length + k, by simp; omega, p, ?_⟩
  rwa [List.take_append, List.take_of_length_le (by omega), run_append,
    show α.length + k - α.length = k by omega]

lemma Dec.of_out {C : Cfg A} {α : List (Ev n)} {p : Fin n} {v : Bool}
    (h : (run C α).Out p v) : Dec C α v :=
  ⟨α.length, le_rfl, p, by rwa [List.take_length]⟩

lemma Dec.of_out_self {C : Cfg A} {p : Fin n} {v : Bool} (h : C.Out p v) (α : List (Ev n)) :
    Dec C α v := ⟨0, Nat.zero_le _, p, by simpa using h⟩

/-- Decisions in `α ++ β` are decisions in `α` or decisions in `β` from `run C α`. -/
lemma Dec.append_cases {C : Cfg A} {α β : List (Ev n)} {v : Bool} (h : Dec C (α ++ β) v) :
    Dec C α v ∨ Dec (run C α) β v := by
  obtain ⟨k, hk, p, hp⟩ := h
  by_cases hkα : k ≤ α.length
  · left
    refine ⟨k, hkα, p, ?_⟩
    rwa [List.take_append_of_le_length hkα] at hp
  · right
    refine ⟨k - α.length, by simp at hk; omega, p, ?_⟩
    rwa [List.take_append, List.take_of_length_le (by omega), run_append] at hp

/-! ## Admissible executions, correctness -/

/-- Number of crashes of `p` in `α`. -/
def crashes (p : Fin n) (α : List (Ev n)) : ℕ := α.count (.crash p)

/-- Is `e` a step of a process with identifier smaller than `p`? -/
def Ev.isStepBelow (p : Fin n) : Ev n → Bool
  | .step q => decide (q < p)
  | .crash _ => false

/-- Number of steps in `α` of processes with identifiers smaller than `p`. -/
def stepsBelow (p : Fin n) (α : List (Ev n)) : ℕ := α.countP (Ev.isStepBelow p)

/-- Ovens' `E_z`: every process `p` crashes at most `z n` times the number of steps taken by
processes with smaller identifiers (in particular `p₀` never crashes). -/
def InE (z : ℕ) (α : List (Ev n)) : Prop := ∀ p, crashes p α ≤ z * n * stepsBelow p α

/-- Ovens' `E*_z`: `InE z` holds for every prefix. -/
def InEs (z : ℕ) (α : List (Ev n)) : Prop := ∀ m, InE z (α.take m)

/-- No crashes. -/
def CrashFree (α : List (Ev n)) : Prop := ∀ p, Ev.crash p ∉ α

/-- The first `t` events of an infinite event sequence. -/
def pre (e : ℕ → Ev n) (t : ℕ) : List (Ev n) := (List.range t).map e

variable (A) in
/-- `A` solves binary consensus on the admissible executions `Adm`: agreement, validity and
progress (see the module docstring). -/
structure Solves (Adm : List (Ev n) → Prop) : Prop where
  agree : ∀ x γ, Adm γ → ∀ v w, Dec (initCfg A x) γ v → Dec (initCfg A x) γ w → v = w
  valid : ∀ x γ, Adm γ → ∀ v, Dec (initCfg A x) γ v → ∃ p, x p = v
  prog : ∀ x (e : ℕ → Ev n) p N, (∀ t, Adm (pre e t)) → (∀ M, ∃ t ≥ M, e t = .step p) →
    (∀ t ≥ N, e t ≠ .crash p) → ∃ t ≥ N, ∃ v, (run (initCfg A x) (pre e t)).Out p v

variable (A) in
/-- Recoverable wait-free (binary) consensus with individual crashes. -/
def RecConsensus : Prop := Solves A (fun _ => True)

variable (A) in
/-- Wait-free (binary) consensus (crash-stop model: no recoveries). -/
def WFConsensus : Prop := Solves A CrashFree

/-! ## Indistinguishability -/

/-- `C` and `D` are indistinguishable to the processes in `Q` (same local states and inputs) and
all objects have the same values. -/
def AgreeOn (Q : Set (Fin n)) (C D : Cfg A) : Prop :=
  C.mem = D.mem ∧ ∀ p ∈ Q, C.loc p = D.loc p ∧ C.inp p = D.inp p

omit [DecidableEq ι] in
lemma AgreeOn.symm {Q : Set (Fin n)} {C D : Cfg A} (h : AgreeOn Q C D) : AgreeOn Q D C :=
  ⟨h.1.symm, fun p hp => ⟨(h.2 p hp).1.symm, (h.2 p hp).2.symm⟩⟩

omit [DecidableEq ι] in
lemma AgreeOn.refl (Q : Set (Fin n)) (C : Cfg A) : AgreeOn Q C C := ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

omit [DecidableEq ι] in
lemma AgreeOn.mono {Q Q' : Set (Fin n)} {C D : Cfg A} (h : AgreeOn Q C D) (hQ : Q' ⊆ Q) :
    AgreeOn Q' C D := ⟨h.1, fun p hp => h.2 p (hQ hp)⟩

omit [DecidableEq ι] in
lemma AgreeOn.out_iff {Q : Set (Fin n)} {C D : Cfg A} (h : AgreeOn Q C D) {p : Fin n}
    (hp : p ∈ Q) (v : Bool) : C.Out p v ↔ D.Out p v := by
  simp [Cfg.Out, (h.2 p hp).1]

lemma next_agreeOn {Q : Set (Fin n)} {C D : Cfg A} (h : AgreeOn Q C D) (e : Ev n)
    (he : e.proc ∈ Q) : AgreeOn Q (C.next e) (D.next e) := by
  obtain ⟨hm, hl⟩ := h
  cases e with
  | step p =>
    have hp : C.loc p = D.loc p := (hl p he).1
    simp only [Cfg.next]
    rcases hact : A.act (C.loc p) with ⟨i, o, k⟩ | v
    · have hact' : A.act (D.loc p) = .access i o k := by rw [← hp]; exact hact
      rw [stepP_of_access C hact, stepP_of_access D hact']
      refine ⟨by simp [hm], fun q hq => ⟨?_, (hl q hq).2⟩⟩
      by_cases hqp : q = p
      · subst hqp; simp [hm]
      · simp [Function.update_of_ne hqp, (hl q hq).1]
    · have hact' : D.Out p v := by rw [Cfg.Out, ← hp]; exact hact
      rw [stepP_of_out C (show C.Out p v from hact), stepP_of_out D hact']
      exact ⟨hm, hl⟩
  | crash p =>
    refine ⟨hm, fun q hq => ⟨?_, (hl q hq).2⟩⟩
    simp only [Cfg.next]
    by_cases hqp : q = p
    · subst hqp; simp [(hl q he).2]
    · simp [Function.update_of_ne hqp, (hl q hq).1]

/-- Executions with events only by `Q` from configurations indistinguishable to `Q` (with the
same object values) stay indistinguishable to `Q`. -/
lemma run_agreeOn {Q : Set (Fin n)} {C D : Cfg A} (h : AgreeOn Q C D) (β : List (Ev n))
    (hβ : ∀ e ∈ β, e.proc ∈ Q) : AgreeOn Q (run C β) (run D β) := by
  induction β generalizing C D with
  | nil => exact h
  | cons e β ih =>
    exact ih (next_agreeOn h e (hβ e (by simp))) (fun e' he' => hβ e' (by simp [he']))

/-- Transfer of decisions along indistinguishable executions (core of Ovens' Observation 5):
processes outside `Q` must not be in an output state in `D`. -/
lemma Dec.of_agreeOn {Q : Set (Fin n)} {C D : Cfg A} (h : AgreeOn Q C D) {β : List (Ev n)}
    (hβ : ∀ e ∈ β, e.proc ∈ Q) (hout : ∀ p ∉ Q, ∀ v, ¬ D.Out p v) {v : Bool} (hd : Dec D β v) :
    Dec C β v := by
  obtain ⟨k, hk, p, hp⟩ := hd
  refine ⟨k, hk, p, ?_⟩
  have hβk : ∀ e ∈ β.take k, e.proc ∈ Q := fun e he => hβ e (List.mem_of_mem_take he)
  by_cases hpQ : p ∈ Q
  · exact ((run_agreeOn h _ hβk).out_iff hpQ v).2 hp
  · exfalso
    apply hout p hpQ v
    have : (run D (β.take k)).loc p = D.loc p :=
      run_loc_other D _ (fun e he hep => hpQ (hep ▸ hβk e he))
    simpa [Cfg.Out, this] using hp

/-! ## Crash budgets (Ovens' `E_z`, `E*_z`) -/

@[simp] lemma crashes_nil (p : Fin n) : crashes p ([] : List (Ev n)) = 0 := rfl

@[simp] lemma crashes_append (p : Fin n) (α β : List (Ev n)) :
    crashes p (α ++ β) = crashes p α + crashes p β := by
  simp [crashes, List.count_append]

@[simp] lemma crashes_cons_step (p q : Fin n) (α : List (Ev n)) :
    crashes p (.step q :: α) = crashes p α := by
  simp [crashes]

@[simp] lemma crashes_cons_crash (p q : Fin n) (α : List (Ev n)) :
    crashes p (.crash q :: α) = crashes p α + if q = p then 1 else 0 := by
  by_cases h : q = p <;> simp [crashes, h]

@[simp] lemma stepsBelow_nil (p : Fin n) : stepsBelow p ([] : List (Ev n)) = 0 := rfl

@[simp] lemma stepsBelow_append (p : Fin n) (α β : List (Ev n)) :
    stepsBelow p (α ++ β) = stepsBelow p α + stepsBelow p β := by
  simp [stepsBelow, List.countP_append]

@[simp] lemma stepsBelow_cons_step (p q : Fin n) (α : List (Ev n)) :
    stepsBelow p (.step q :: α) = stepsBelow p α + if q < p then 1 else 0 := by
  by_cases h : q < p <;> simp [stepsBelow, Ev.isStepBelow, h]

@[simp] lemma stepsBelow_cons_crash (p q : Fin n) (α : List (Ev n)) :
    stepsBelow p (.crash q :: α) = stepsBelow p α := by
  simp [stepsBelow, Ev.isStepBelow]

lemma stepsBelow_zero (α : List (Ev n)) (p : Fin n) (hp : p.val = 0) : stepsBelow p α = 0 := by
  induction α with
  | nil => rfl
  | cons e α ih =>
    cases e with
    | step q =>
      have : ¬ q < p := by rw [Fin.lt_def]; omega
      simp [this, ih]
    | crash q => simp [ih]

lemma crashes_eq_zero_of_crashFree {α : List (Ev n)} (h : CrashFree α) (p : Fin n) :
    crashes p α = 0 := List.count_eq_zero.2 (h p)

lemma InE.of_crashFree {α : List (Ev n)} (h : CrashFree α) (z : ℕ) : InE z α := by
  intro p; simp [crashes_eq_zero_of_crashFree h]

lemma CrashFree.take {α : List (Ev n)} (h : CrashFree α) (m : ℕ) : CrashFree (α.take m) :=
  fun p hp => h p (List.mem_of_mem_take hp)

lemma CrashFree.append {α β : List (Ev n)} (h : CrashFree α) (h' : CrashFree β) :
    CrashFree (α ++ β) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h p hp
  · exact h' p hp

lemma CrashFree.of_append_left {α β : List (Ev n)} (h : CrashFree (α ++ β)) : CrashFree α :=
  fun p hp => h p (List.mem_append_left _ hp)

lemma CrashFree.of_append_right {α β : List (Ev n)} (h : CrashFree (α ++ β)) : CrashFree β :=
  fun p hp => h p (List.mem_append_right _ hp)

lemma crashFree_steps (l : List (Fin n)) : CrashFree (l.map Ev.step) := by
  intro p hp; simp at hp

lemma crashFree_replicate (k : ℕ) (p : Fin n) : CrashFree (List.replicate k (Ev.step p)) := by
  intro q hq; simp [List.mem_replicate] at hq

lemma crashFree_of_inE_zero {α : List (Ev n)} (h : InE 0 α) : CrashFree α := by
  intro p hp
  have := h p
  simp only [zero_mul, Nat.le_zero, crashes] at this
  exact (List.count_eq_zero.1 this) hp

lemma InEs.of_crashFree {α : List (Ev n)} (h : CrashFree α) (z : ℕ) : InEs z α :=
  fun m => InE.of_crashFree (h.take m) z

lemma InE.append {z : ℕ} {α β : List (Ev n)} (h : InE z α) (h' : InE z β) :
    InE z (α ++ β) := by
  intro p
  have := h p; have := h' p
  simp only [crashes_append, stepsBelow_append, mul_add]
  omega

lemma InE.mono {z z' : ℕ} (hz : z ≤ z') {α : List (Ev n)} (h : InE z α) : InE z' α := by
  intro p
  exact (h p).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hz))

lemma InEs.inE {z : ℕ} {α : List (Ev n)} (h : InEs z α) : InE z α := by
  simpa using h α.length

lemma InEs.mono {z z' : ℕ} (hz : z ≤ z') {α : List (Ev n)} (h : InEs z α) : InEs z' α :=
  fun m => (h m).mono hz

/-- Ovens' Observation 3 for `E*_z`. -/
lemma InEs.append {z : ℕ} {α β : List (Ev n)} (h : InEs z α) (h' : InEs z β) :
    InEs z (α ++ β) := by
  intro m
  rw [List.take_append]
  exact (h m).append (h' _)

lemma InEs.of_append_left {z : ℕ} {α β : List (Ev n)} (h : InEs z (α ++ β)) : InEs z α := by
  intro m
  by_cases hm : m ≤ α.length
  · have := h m
    rwa [List.take_append_of_le_length hm] at this
  · have := h α.length
    rw [List.take_append_of_le_length le_rfl, List.take_length] at this
    rwa [List.take_of_length_le (by omega)]

/-- Ovens' Observation 4: appending crash-free events preserves `E*_z`. -/
lemma InEs.append_crashFree {z : ℕ} {α β : List (Ev n)} (h : InEs z α) (h' : CrashFree β) :
    InEs z (α ++ β) := h.append (InEs.of_crashFree h' z)

lemma InEs.nil (z : ℕ) : InEs z ([] : List (Ev n)) := fun m => by intro p; simp

/-- Processes that take no steps of smaller processes cannot crash. -/
lemma InE.crashes_eq_zero {z : ℕ} {α : List (Ev n)} (h : InE z α) {p : Fin n}
    (hp : stepsBelow p α = 0) : crashes p α = 0 := by
  have := h p; rw [hp] at this; simpa using this

/-! ## Reachability and progress -/

/-- Conditions on the admissible executions used by the valency arguments: closed under
appending executions in `E_z` and under prefixes. Satisfied by `fun _ => True` (any `z`) and by
`CrashFree` (`z = 0`). -/
structure AdmOK (Adm : List (Ev n) → Prop) (z : ℕ) : Prop where
  nil : Adm []
  append : ∀ γ β, Adm γ → InE z β → Adm (γ ++ β)
  pre_closed : ∀ γ β, Adm (γ ++ β) → Adm γ

lemma admOK_true (z : ℕ) : AdmOK (fun _ : List (Ev n) => True) z :=
  ⟨trivial, fun _ _ _ _ => trivial, fun _ _ _ => trivial⟩

lemma admOK_crashFree : AdmOK (CrashFree (n := n)) 0 :=
  ⟨fun _ h => by simp at h, fun _ _ h h' => h.append (crashFree_of_inE_zero h'),
    fun _ _ h => h.of_append_left⟩

lemma AdmOK.mono {Adm : List (Ev n) → Prop} {z z' : ℕ} (h : AdmOK Adm z') (hz : z ≤ z') :
    AdmOK Adm z := ⟨h.nil, fun γ β hγ hβ => h.append γ β hγ (hβ.mono hz), h.pre_closed⟩

variable (A) in
/-- `C` is reachable from an initial configuration by an admissible execution. -/
def Reach (Adm : List (Ev n) → Prop) (C : Cfg A) : Prop :=
  ∃ x γ, Adm γ ∧ run (initCfg A x) γ = C

section Reach

variable {Adm : List (Ev n) → Prop} {z : ℕ}

lemma Reach.run {C : Cfg A} (hC : Reach A Adm C) (hAdm : AdmOK Adm z) {β : List (Ev n)}
    (hβ : InE z β) : Reach A Adm (run C β) := by
  obtain ⟨x, γ, hγ, rfl⟩ := hC
  exact ⟨x, γ ++ β, hAdm.append _ _ hγ hβ, by rw [run_append]⟩

lemma Reach.initial (hAdm : AdmOK Adm z) (x : Fin n → Bool) : Reach A Adm (initCfg A x) :=
  ⟨x, [], hAdm.nil, rfl⟩

/-- Agreement from a reachable configuration. -/
lemma Solves.agree_of_reach (hA : Solves A Adm) (hAdm : AdmOK Adm z) {C : Cfg A}
    (hC : Reach A Adm C) {β : List (Ev n)} (hβ : InE z β) {v w : Bool} (hv : Dec C β v)
    (hw : Dec C β w) : v = w := by
  obtain ⟨x, γ, hγ, rfl⟩ := hC
  exact hA.agree x (γ ++ β) (hAdm.append _ _ hγ hβ) v w hv.of_suffix hw.of_suffix

end Reach

/-! ## Infinite executions -/

lemma pre_zero (e : ℕ → Ev n) : pre e 0 = [] := rfl

lemma pre_succ (e : ℕ → Ev n) (t : ℕ) : pre e (t + 1) = pre e t ++ [e t] := by
  simp [pre, List.range_succ]

@[simp] lemma pre_length (e : ℕ → Ev n) (t : ℕ) : (pre e t).length = t := by simp [pre]

lemma pre_add (e : ℕ → Ev n) (a b : ℕ) :
    pre e (a + b) = pre e a ++ pre (fun i => e (a + i)) b := by
  induction b with
  | zero => simp [pre_zero]
  | succ b ih => rw [← Nat.add_assoc, pre_succ, ih, pre_succ, List.append_assoc]

lemma pre_prefix (e : ℕ → Ev n) {t t' : ℕ} (h : t ≤ t') :
    ∃ δ, pre e t' = pre e t ++ δ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨_, pre_add e t d⟩

lemma getElem_pre (e : ℕ → Ev n) (t i : ℕ) (hi : i < (pre e t).length) :
    (pre e t)[i] = e i := by simp [pre]

section Reach

variable {Adm : List (Ev n) → Prop} {z : ℕ}

/-- Progress (recoverable wait-freedom) applied to an infinite execution from a reachable
configuration: the process outputs at some time `≥ N`. -/
lemma Solves.prog_of_reach (hA : Solves A Adm) (hAdm : AdmOK Adm z) {C : Cfg A}
    (hC : Reach A Adm C) (e : ℕ → Ev n) (p : Fin n) (N : ℕ)
    (he : ∀ t, ∃ t' ≥ t, InE z (pre e t')) (hinf : ∀ M, ∃ t ≥ M, e t = .step p)
    (hN : ∀ t ≥ N, e t ≠ .crash p) : ∃ t ≥ N, ∃ v, (run C (pre e t)).Out p v := by
  classical
  obtain ⟨x, γ, hγ, rfl⟩ := hC
  set e' : ℕ → Ev n := fun t => if h : t < γ.length then γ[t] else e (t - γ.length) with he'
  have hshift : (fun i => e' (γ.length + i)) = e := by
    funext i; simp [he']
  have hpreγ : pre e' γ.length = γ := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    rw [getElem_pre]
    simp [he', h2]
  have hpre : ∀ t, pre e' (γ.length + t) = γ ++ pre e t := by
    intro t; rw [pre_add, hpreγ, hshift]
  have hadm : ∀ t, Adm (pre e' t) := by
    intro t
    obtain ⟨t', ht', hE⟩ := he t
    have h1 : Adm (pre e' (γ.length + t')) := by
      rw [hpre]; exact hAdm.append _ _ hγ hE
    obtain ⟨δ, hδ⟩ := pre_prefix e' (show t ≤ γ.length + t' by omega)
    rw [hδ] at h1
    exact hAdm.pre_closed _ _ h1
  have hinf' : ∀ M, ∃ t ≥ M, e' t = .step p := by
    intro M
    obtain ⟨t, ht, het⟩ := hinf M
    refine ⟨γ.length + t, by omega, ?_⟩
    simp [he', het]
  have hN' : ∀ t ≥ γ.length + N, e' t ≠ .crash p := by
    intro t ht
    simp only [he', show ¬ t < γ.length by omega, dite_false]
    exact hN _ (by omega)
  obtain ⟨t, ht, v, hv⟩ := hA.prog x e' p (γ.length + N) hadm hinf' hN'
  obtain ⟨t₀, rfl⟩ := Nat.exists_eq_add_of_le (show γ.length ≤ t by omega)
  refine ⟨t₀, by omega, v, ?_⟩
  rwa [hpre, run_append] at hv

/-! ## Solo runs -/

/-- `k` steps of `p`. -/
abbrev solo (p : Fin n) (k : ℕ) : List (Ev n) := List.replicate k (.step p)

lemma run_solo_of_out {D : Cfg A} {p : Fin n} {v : Bool} (h : D.Out p v) (k : ℕ) :
    run D (solo p k) = D := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change run D (.step p :: solo p k) = D
    rw [run_cons]
    simp only [Cfg.next, stepP_of_out D h]
    exact ih

lemma solo_add (p : Fin n) (a b : ℕ) : solo p (a + b) = solo p a ++ solo p b :=
  List.replicate_add _ _ _

/-- `p`, running solo (without crashes) from `C`, outputs `v`. -/
def SoloOut (C : Cfg A) (p : Fin n) (v : Bool) : Prop := ∃ k, (run C (solo p k)).Out p v

lemma SoloOut.unique {C : Cfg A} {p : Fin n} {v w : Bool} (hv : SoloOut C p v)
    (hw : SoloOut C p w) : v = w := by
  obtain ⟨k, hk⟩ := hv
  obtain ⟨j, hj⟩ := hw
  have e1 : run C (solo p (k + j)) = run C (solo p k) := by
    rw [solo_add, run_append, run_solo_of_out hk]
  have e2 : run C (solo p (k + j)) = run C (solo p j) := by
    rw [Nat.add_comm, solo_add, run_append, run_solo_of_out hj]
  have : (run C (solo p (k + j))).Out p v := by rw [e1]; exact hk
  rw [e2] at this
  unfold Cfg.Out at this hj
  rw [this] at hj
  simpa using hj

lemma SoloOut.of_agreeOn {C D : Cfg A} {p : Fin n} {v : Bool} (h : AgreeOn {p} C D)
    (hv : SoloOut C p v) : SoloOut D p v := by
  obtain ⟨k, hk⟩ := hv
  refine ⟨k, ?_⟩
  have := run_agreeOn h (solo p k) (fun e he => by simp [List.mem_replicate] at he; simp [he.2])
  exact (this.out_iff (by simp) v).1 hk

lemma SoloOut.dec {C : Cfg A} {α : List (Ev n)} {p : Fin n} {v : Bool}
    (h : SoloOut (run C α) p v) : ∃ k, Dec C (α ++ solo p k) v := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, Dec.of_out (by rwa [run_append])⟩

lemma SoloOut.of_step {C : Cfg A} {p : Fin n} {v : Bool} (h : SoloOut (C.next (.step p)) p v) :
    SoloOut C p v := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by rwa [Nat.add_comm, solo_add, run_append]⟩

lemma SoloOut.of_out {C : Cfg A} {p : Fin n} {v : Bool} (h : C.Out p v) : SoloOut C p v :=
  ⟨0, h⟩

/-- Solo termination: from a reachable configuration, a process running solo outputs. -/
lemma Solves.exists_soloOut (hA : Solves A Adm) (hAdm : AdmOK Adm z) {C : Cfg A}
    (hC : Reach A Adm C) (p : Fin n) : ∃ v, SoloOut C p v := by
  have hpre : ∀ t, pre (fun _ => Ev.step p) t = solo p t := by
    intro t; simp [pre, solo, List.map_const']
  obtain ⟨t, -, v, hv⟩ := hA.prog_of_reach hAdm hC (fun _ => .step p) p 0
    (fun t => ⟨t, le_rfl, by rw [hpre]; exact InE.of_crashFree (crashFree_replicate _ _) z⟩)
    (fun M => ⟨M, le_rfl, rfl⟩) (fun _ _ => by simp)
  exact ⟨v, t, by rwa [← hpre]⟩

end Reach

/-! ## Valency (Ovens, Section 3) -/

section Valency

variable (z : ℕ) (C : Cfg A)

/-- `Q` is `v`-univalent in `α` w.r.t. `E*_z(C)`: every extension of `α` by events of `Q` that
stays in `E*_z(C)` decides only `v`. -/
def UnivQ (Q : Set (Fin n)) (α : List (Ev n)) (v : Bool) : Prop :=
  InEs z α ∧ ∀ β, (∀ e ∈ β, e.proc ∈ Q) → InEs z (α ++ β) → ∀ w, Dec C (α ++ β) w → w = v

/-- `α` is `v`-univalent w.r.t. `E*_z(C)`. -/
def Univ (α : List (Ev n)) (v : Bool) : Prop := UnivQ z C Set.univ α v

/-- `α` is bivalent w.r.t. `E*_z(C)`. -/
def Biv (α : List (Ev n)) : Prop := ∀ v, ∃ β, InEs z (α ++ β) ∧ Dec C (α ++ β) v

/-- `α` is critical w.r.t. `E*_z(C)`. -/
def Crit (α : List (Ev n)) : Prop :=
  InEs z α ∧ Biv z C α ∧ ∀ β, β ≠ [] → InEs z (α ++ β) → ∃ v, Univ z C (α ++ β) v

/-- `p` is on team `v` in `Cα` (w.r.t. `E*_z(C)`): `αp` is `v`-univalent. -/
def Team (α : List (Ev n)) (p : Fin n) (v : Bool) : Prop := Univ z C (α ++ [.step p]) v

variable {z C}

lemma UnivQ.append {Q : Set (Fin n)} {α β : List (Ev n)} {v : Bool} (h : UnivQ z C Q α v)
    (hβ : ∀ e ∈ β, e.proc ∈ Q) (hs : InEs z (α ++ β)) : UnivQ z C Q (α ++ β) v := by
  refine ⟨hs, fun γ hγ hs' w hw => h.2 (β ++ γ) ?_ (by simpa using hs') w (by simpa using hw)⟩
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact hβ e he
  · exact hγ e he

lemma Univ.append {α β : List (Ev n)} {v : Bool} (h : Univ z C α v)
    (hs : InEs z (α ++ β)) : Univ z C (α ++ β) v :=
  UnivQ.append h (fun _ _ => trivial) hs

lemma Univ.not_biv {α : List (Ev n)} {v : Bool} (h : Univ z C α v) : ¬ Biv z C α := by
  intro hb
  obtain ⟨β, hs, hd⟩ := hb (!v)
  have := h.2 β (fun _ _ => trivial) hs (!v) hd
  cases v <;> simp at this

variable {Adm : List (Ev n) → Prop}

/-- A univalent extension: a process of `Q` running solo outputs the univalent value. -/
lemma UnivQ.soloOut (hA : Solves A Adm) (hAdm : AdmOK Adm z) (hC : Reach A Adm C)
    {Q : Set (Fin n)} {α : List (Ev n)} {v : Bool} (h : UnivQ z C Q α v) {p : Fin n}
    (hp : p ∈ Q) : SoloOut (run C α) p v := by
  obtain ⟨w, hw⟩ := hA.exists_soloOut hAdm (hC.run hAdm h.1.inE) p
  obtain ⟨k, hk⟩ := hw.dec
  have : w = v := h.2 (solo p k) (fun e he => by
    simp [List.mem_replicate] at he; simp [he.2, hp])
    (h.1.append_crashFree (crashFree_replicate _ _)) w hk
  rwa [this] at hw

lemma Team.soloOut (hA : Solves A Adm) (hAdm : AdmOK Adm z) (hC : Reach A Adm C)
    {α : List (Ev n)} {p : Fin n} {v : Bool} (h : Team z C α p v) : SoloOut (run C α) p v := by
  have := UnivQ.soloOut hA hAdm hC h (Set.mem_univ p)
  rw [run_concat] at this
  exact this.of_step

lemma Team.unique (hA : Solves A Adm) (hAdm : AdmOK Adm z) (hC : Reach A Adm C)
    {α : List (Ev n)} {p : Fin n} {v w : Bool} (hv : Team z C α p v) (hw : Team z C α p w) :
    v = w :=
  (hv.soloOut hA hAdm hC).unique (hw.soloOut hA hAdm hC)

lemma Crit.team (hc : Crit z C α) (p : Fin n) : ∃ v, Team z C α p v :=
  hc.2.2 [.step p] (by simp) (hc.1.append_crashFree (crashFree_steps [p]))

/-- At a critical configuration no process is in an output state. -/
lemma Crit.not_out (hA : Solves A Adm) (hAdm : AdmOK Adm z) (hC : Reach A Adm C)
    {α : List (Ev n)} (hc : Crit z C α) (p : Fin n) (v : Bool) : ¬ (run C α).Out p v := by
  intro h
  obtain ⟨β, hs, hd⟩ := hc.2.1 (!v)
  have := hA.agree_of_reach hAdm hC hs.inE hd ((Dec.of_out h).append_right β)
  cases v <;> simp at this

/-- If two processes on different teams reach configurations indistinguishable to `r` (with the
same object values), we get a contradiction (`r` decides the same value in both). -/
lemma team_contra (hA : Solves A Adm) (hAdm : AdmOK Adm z) (hC : Reach A Adm C)
    {α : List (Ev n)} {p q r : Fin n} {v : Bool} (hp : Team z C α p v) (hq : Team z C α q (!v))
    {β β' : List (Ev n)} (hβ : InEs z (α ++ [.step p] ++ β))
    (hβ' : InEs z (α ++ [.step q] ++ β'))
    (hag : AgreeOn {r} (run C (α ++ [.step p] ++ β)) (run C (α ++ [.step q] ++ β'))) : False := by
  have h1 := UnivQ.soloOut hA hAdm hC (Univ.append hp hβ) (Set.mem_univ r)
  have h2 := UnivQ.soloOut hA hAdm hC (Univ.append hq hβ') (Set.mem_univ r)
  have := (h1.of_agreeOn hag).unique h2
  cases v <;> simp at this

end Valency

/-! ## Ovens' Lemma 6: no infinite bivalent chains -/

section Chain

variable {Adm : List (Ev n) → Prop} {z : ℕ}

/-- The core of Ovens' Lemma 6: there is no infinite strictly increasing chain of executions in
`E_z(C)` each of which can still be extended to decide both values. (The process with the
smallest identifier taking infinitely many steps crashes finitely often, so it outputs by
recoverable wait-freedom; agreement is then violated.) -/
theorem no_chain (hA : Solves A Adm) (hAdm : AdmOK Adm z) {C : Cfg A} (hC : Reach A Adm C)
    (g : ℕ → List (Ev n)) (hg : ∀ i, ∃ δ, δ ≠ [] ∧ g (i + 1) = g i ++ δ)
    (hE : ∀ i, InE z (g i))
    (hbiv : ∀ i v, ∃ β, InE z (g i ++ β) ∧ Dec C (g i ++ β) v) : False := by
  classical
  -- lengths and prefixes
  have hmono : ∀ i j, i ≤ j → ∃ δ, g j = g i ++ δ := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact ⟨[], by simp⟩
    | succ j _ ih =>
      obtain ⟨δ, hδ⟩ := ih
      obtain ⟨δ', -, hδ'⟩ := hg j
      exact ⟨δ ++ δ', by rw [hδ', hδ, List.append_assoc]⟩
  have hlen : ∀ i, i ≤ (g i).length := by
    intro i
    induction i with
    | zero => omega
    | succ i ih =>
      obtain ⟨δ, hδ, h⟩ := hg i
      rw [h, List.length_append]
      have := List.length_pos_iff.2 hδ
      omega
  let e : ℕ → Ev n := fun t => (g (t + 1))[t]'(by have := hlen (t + 1); omega)
  have he : ∀ i t (ht : t < (g i).length), e t = (g i)[t] := by
    intro i t ht
    simp only [e]
    rcases le_total (t + 1) i with h | h
    · obtain ⟨δ, hδ⟩ := hmono _ _ h
      simp only [hδ]
      rw [List.getElem_append_left]
    · obtain ⟨δ, hδ⟩ := hmono _ _ h
      simp only [hδ]
      rw [List.getElem_append_left]
  have hpre : ∀ i, pre e (g i).length = g i := by
    intro i
    apply List.ext_getElem (by simp)
    intro t h1 h2
    rw [getElem_pre]
    exact he i t h2
  have hpre_le : ∀ t i, t ≤ (g i).length → ∃ δ, g i = pre e t ++ δ := by
    intro t i h
    obtain ⟨δ, hδ⟩ := pre_prefix e h
    exact ⟨δ, by rw [← hpre i, hδ]⟩
  -- some process has infinitely many events
  let Inf : Fin n → Prop := fun q => ∀ M, ∃ t ≥ M, (e t).proc = q
  have hex : ∃ q, Inf q := by
    by_contra hno
    have hno' : ∀ q, ∃ N, ∀ t ≥ N, (e t).proc ≠ q := by
      intro q
      have : ¬ Inf q := fun h => hno ⟨q, h⟩
      simp only [Inf, not_forall, not_exists, not_and] at this
      obtain ⟨N, hN⟩ := this
      exact ⟨N, fun t ht => hN t ht⟩
    choose N hN using hno'
    let M := Finset.univ.sup N
    exact hN (e M).proc M (Finset.le_sup (Finset.mem_univ _)) rfl
  -- the smallest one
  let S := Finset.univ.filter Inf
  have hS : S.Nonempty := by obtain ⟨q, hq⟩ := hex; exact ⟨q, by simp [S, hq]⟩
  let k₀ := S.min' hS
  have hk₀ : Inf k₀ := by have := S.min'_mem hS; simpa [S] using this
  have hbelow : ∀ q < k₀, ¬ Inf q := by
    intro q hq hInf
    have := S.min'_le q (by simp [S, hInf])
    exact absurd hq (not_lt.2 this)
  have hbelow' : ∀ q, ∃ N, q < k₀ → ∀ t ≥ N, (e t).proc ≠ q := by
    intro q
    by_cases hq : q < k₀
    · have := hbelow q hq
      simp only [Inf, not_forall, not_exists, not_and] at this
      obtain ⟨N, hN⟩ := this
      exact ⟨N, fun _ t ht => hN t ht⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose Nq hNq using hbelow'
  let N₁ := (Finset.univ.filter (· < k₀)).sup Nq
  have hN₁ : ∀ t ≥ N₁, ¬ (e t).proc < k₀ := by
    intro t ht hlt
    exact hNq _ hlt t (le_trans (Finset.le_sup (f := Nq) (by simp [hlt])) ht) rfl
  -- steps of smaller processes stop
  have hsteps : ∀ t ≥ N₁, stepsBelow k₀ (pre e t) = stepsBelow k₀ (pre e N₁) := by
    intro t ht
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [pre_add, stepsBelow_append]
    suffices stepsBelow k₀ (pre (fun i => e (N₁ + i)) d) = 0 by omega
    unfold stepsBelow
    rw [List.countP_eq_zero]
    intro a ha
    simp only [pre, List.mem_map, List.mem_range] at ha
    obtain ⟨i, -, rfl⟩ := ha
    have := hN₁ (N₁ + i) (by omega)
    cases h : e (N₁ + i) with
    | step q => rw [h] at this; simpa [Ev.isStepBelow] using this
    | crash q => simp [Ev.isStepBelow]
  -- crashes of k₀ are bounded
  let B := z * n * stepsBelow k₀ (pre e N₁)
  have hcr_mono : ∀ t t', t ≤ t' → crashes k₀ (pre e t) ≤ crashes k₀ (pre e t') := by
    intro t t' h
    obtain ⟨δ, hδ⟩ := pre_prefix e h
    rw [hδ, crashes_append]; omega
  have hbound : ∀ t, crashes k₀ (pre e t) ≤ B := by
    intro t
    have hl := hlen (t + N₁)
    refine (hcr_mono t (g (t + N₁)).length (by omega)).trans ?_
    rw [hpre]
    refine (hE (t + N₁) k₀).trans (le_of_eq ?_)
    rw [← hpre, hsteps _ (by omega)]
  -- hence eventually no crash of k₀
  have hstab : ∃ N₂, ∀ t ≥ N₂, crashes k₀ (pre e (t + 1)) = crashes k₀ (pre e t) := by
    by_contra hno
    push Not at hno
    have : ∀ m, ∃ t, m ≤ crashes k₀ (pre e t) := by
      intro m
      induction m with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ m ih =>
        obtain ⟨t, ht⟩ := ih
        obtain ⟨t', ht', hne⟩ := hno t
        have h1 := hcr_mono t t' ht'
        have h2 := hcr_mono t' (t' + 1) (by omega)
        exact ⟨t' + 1, by omega⟩
    obtain ⟨t, ht⟩ := this (B + 1)
    have := hbound t
    omega
  obtain ⟨N₂, hN₂⟩ := hstab
  have hnocrash : ∀ t ≥ N₂, e t ≠ .crash k₀ := by
    intro t ht hc
    have := hN₂ t ht
    rw [pre_succ, crashes_append, hc] at this
    simp [crashes] at this
  have hinfstep : ∀ M, ∃ t ≥ M, e t = .step k₀ := by
    intro M
    obtain ⟨t, ht, hp⟩ := hk₀ (max M N₂)
    refine ⟨t, le_trans (le_max_left _ _) ht, ?_⟩
    cases h : e t with
    | step q => rw [h] at hp; simp only [Ev.proc_step] at hp; rw [hp]
    | crash q =>
      rw [h] at hp; simp only [Ev.proc_crash] at hp
      exact absurd (hp ▸ h) (hnocrash t (le_trans (le_max_right _ _) ht))
  -- apply progress
  obtain ⟨t, -, v, hv⟩ := hA.prog_of_reach hAdm hC e k₀ N₂
    (fun t => ⟨(g t).length, hlen t, by rw [hpre]; exact hE t⟩) hinfstep (fun t ht => hnocrash t ht)
  obtain ⟨δ, hδ⟩ := hpre_le t t (hlen t)
  have hd : Dec C (g t) v := by rw [hδ]; exact (Dec.of_out hv).append_right δ
  obtain ⟨β, hβ, hdβ⟩ := hbiv t (!v)
  have := hA.agree_of_reach hAdm hC hβ hdβ (hd.append_right β)
  cases v <;> simp at this

/-- Iterating a strict-extension function gives an infinite chain. -/
private lemma chain_of_step {P : List (Ev n) → Prop} (x₀ : List (Ev n)) (h₀ : P x₀)
    (hstep : ∀ x, P x → ∃ δ, δ ≠ [] ∧ P (x ++ δ)) :
    ∃ g : ℕ → List (Ev n), g 0 = x₀ ∧ (∀ i, P (g i)) ∧ ∀ i, ∃ δ, δ ≠ [] ∧ g (i + 1) = g i ++ δ := by
  choose! d hd using hstep
  let f : ℕ → List (Ev n) := fun i => Nat.rec x₀ (fun _ x => x ++ d x) i
  have hf : ∀ i, P (f i) := by
    intro i
    induction i with
    | zero => exact h₀
    | succ i ih => exact (hd _ ih).2
  exact ⟨f, rfl, hf, fun i => ⟨d (f i), (hd _ (hf i)).1, rfl⟩⟩

/-- **Ovens' Lemma 6 (a).** If `C` is bivalent w.r.t. `E*_z(C)`, there is a finite execution
`α ∈ E*_z(C)` that is critical w.r.t. `E*_z(C)`. -/
theorem exists_crit (hA : Solves A Adm) (hAdm : AdmOK Adm z) {C : Cfg A} (hC : Reach A Adm C)
    (hb : Biv z C []) : ∃ α, Crit z C α := by
  by_contra hno
  push Not at hno
  have hstep : ∀ α, (InEs z α ∧ Biv z C α) →
      ∃ δ, δ ≠ [] ∧ (InEs z (α ++ δ) ∧ Biv z C (α ++ δ)) := by
    rintro α ⟨hs, hb⟩
    have := hno α
    simp only [Crit, not_and, not_forall, not_exists] at this
    obtain ⟨β, hβ, hsβ, hnu⟩ := this hs hb
    refine ⟨β, hβ, hsβ, fun v => ?_⟩
    have := hnu (!v)
    simp only [Univ, UnivQ, not_and, not_forall] at this
    obtain ⟨γ, -, hsγ, w, hw, hne⟩ := this hsβ
    have : w = v := by cases v <;> cases w <;> simp_all
    subst this
    exact ⟨γ, by simpa using hsγ, by simpa using hw⟩
  obtain ⟨g, -, hP, hg⟩ := chain_of_step (P := fun α => InEs z α ∧ Biv z C α) []
    ⟨InEs.nil z, hb⟩ hstep
  refine no_chain hA hAdm hC g hg (fun i => (hP i).1.inE) (fun i v => ?_)
  obtain ⟨β, hs, hd⟩ := (hP i).2 v
  exact ⟨β, hs.inE, hd⟩

/-- **Ovens' Lemma 6 (b).** For `z ≤ z'`: there is `β ∈ E_{z'}(C)` such that `Cβ` is bivalent
w.r.t. `E*_z(Cβ)` and no nonempty extension `βγ ∈ E_{z'}(C)` has `Cβγ` bivalent w.r.t.
`E*_z(Cβγ)`. -/
theorem exists_stuck {z' : ℕ} (hzz : z ≤ z') (hA : Solves A Adm) (hAdm : AdmOK Adm z')
    {C : Cfg A} (hC : Reach A Adm C) (hb : Biv z C []) :
    ∃ β, InE z' β ∧ Biv z (run C β) [] ∧
      ∀ γ, γ ≠ [] → InE z' (β ++ γ) → ¬ Biv z (run C (β ++ γ)) [] := by
  by_contra hno
  push Not at hno
  obtain ⟨g, -, hP, hg⟩ := chain_of_step (P := fun β => InE z' β ∧ Biv z (run C β) []) []
    ⟨fun p => by simp, by simpa using hb⟩ (fun β ⟨h1, h2⟩ => by
      obtain ⟨γ, hγ, h3, h4⟩ := hno β h1 h2
      exact ⟨γ, hγ, h3, h4⟩)
  refine no_chain hA hAdm hC g hg (fun i => (hP i).1) (fun i v => ?_)
  obtain ⟨β, hs, hd⟩ := (hP i).2 v
  simp only [List.nil_append] at hs hd
  exact ⟨β, (hP i).1.append ((hs.inE).mono hzz), hd.of_suffix⟩

end Chain

/-! ## Ovens' Observation 1 and Lemmas 7–9 -/

section Crit

variable {Adm : List (Ev n) → Prop} {z : ℕ}

/-- **Ovens' Observation 1.** An initial configuration in which some process has input `0` and
another has input `1` is bivalent w.r.t. `E*_z`. -/
theorem biv_initial (hA : Solves A Adm) (hAdm : AdmOK Adm z) (x : Fin n → Bool)
    (h0 : ∃ p, x p = false) (h1 : ∃ q, x q = true) : Biv z (initCfg A x) [] := by
  have key : ∀ p b, x p = b → ∃ k, Dec (initCfg A x) (solo p k) b := by
    intro p b hpb
    obtain ⟨w, k, hk⟩ := hA.exists_soloOut hAdm (Reach.initial hAdm (fun _ => b)) p
    have hag : AgreeOn {p} (initCfg A (fun _ => b)) (initCfg A x) :=
      ⟨rfl, fun q hq => by simp only [Set.mem_singleton_iff] at hq; subst hq; simp [initCfg, hpb]⟩
    have hk' := ((run_agreeOn hag (solo p k) (fun e he => by
      simp [List.mem_replicate] at he; simp [he.2])).out_iff (by simp) w).1 hk
    obtain ⟨r, hr⟩ := hA.valid (fun _ => b) (solo p k)
      (by simpa using hAdm.append [] _ hAdm.nil (InE.of_crashFree (crashFree_replicate _ _) z))
      w (Dec.of_out hk)
    subst hr
    exact ⟨k, Dec.of_out hk'⟩
  intro v
  obtain ⟨p, hp⟩ : ∃ p, x p = v := by cases v; exacts [h0, h1]
  obtain ⟨k, hk⟩ := key p v hp
  exact ⟨solo p k, by simpa using InEs.of_crashFree (crashFree_replicate k p) z, by simpa using hk⟩

variable {C : Cfg A}

/-- **Ovens' Lemma 7.** At a critical execution there is a process on team `0` and a process
on team `1`. -/
theorem Crit.teams (hA : Solves A Adm) (hAdm : AdmOK Adm z) (hC : Reach A Adm C) (hn : 0 < n)
    {α : List (Ev n)} (hc : Crit z C α) :
    (∃ p, Team z C α p false) ∧ (∃ q, Team z C α q true) := by
  let p₀ : Fin n := ⟨0, hn⟩
  obtain ⟨v, hv⟩ := hc.team p₀
  suffices ∃ q, Team z C α q (!v) by
    cases v
    · exact ⟨⟨p₀, hv⟩, this⟩
    · exact ⟨this, ⟨p₀, hv⟩⟩
  obtain ⟨β, hs, hd⟩ := hc.2.1 (!v)
  have hsolo := hv.soloOut hA hAdm hC
  rcases β with _ | ⟨e, β⟩
  · exfalso
    have hs1 : InEs z (α ++ [.step p₀] ++ []) := by
      rw [List.append_nil]; exact hc.1.append_crashFree (crashFree_steps [p₀])
    have hd1 : Dec C (α ++ [.step p₀] ++ []) (!v) := by
      rw [List.append_nil]; exact (by simpa using hd : Dec C α (!v)).append_right _
    have := hv.2 [] (fun _ h => by simp at h) hs1 (!v) hd1
    cases v <;> simp at this
  cases e with
  | step q =>
    obtain ⟨w, hw⟩ := hc.team q
    have := hw.2 β (fun _ _ => trivial) (by simpa using hs) (!v) (by simpa using hd)
    exact ⟨q, by rw [← this] at hw; exact hw⟩
  | crash q =>
    exfalso
    have hsc : InEs z (α ++ [.crash q]) := by
      have h' : InEs z ((α ++ [.crash q]) ++ β) := by simpa using hs
      exact h'.of_append_left
    have hq : q ≠ p₀ := by
      rintro rfl
      have h1 := hsc.inE p₀
      rw [stepsBelow_zero _ p₀ rfl, crashes_append] at h1
      simp [crashes] at h1
    obtain ⟨w, hw⟩ := hc.2.2 [.crash q] (by simp) hsc
    -- p₀'s solo run after the crash of q decides v
    have hag : AgreeOn {p₀} (run C α) (run C (α ++ [.crash q])) := by
      rw [run_concat]
      refine ⟨rfl, fun r hr => ?_⟩
      simp only [Set.mem_singleton_iff] at hr; subst hr
      exact ⟨(next_loc_other _ _ (by simpa using hq.symm)).symm, by simp⟩
    obtain ⟨k, hk⟩ := (hsolo.of_agreeOn hag).dec
    have e1 := hw.2 (solo p₀ k) (fun _ _ => trivial)
      (hsc.append_crashFree (crashFree_replicate _ _)) v hk
    have e2 := hw.2 β (fun _ _ => trivial) (by simpa using hs) (!v) (by simpa using hd)
    rw [← e1] at e2
    cases v <;> simp at e2

/-- **Ovens' Lemma 8.** If `α` is critical w.r.t. `E*_z(C)`, then `Cα` is bivalent w.r.t.
`E*_z(Cα)`. -/
theorem Crit.biv (hA : Solves A Adm) (hAdm : AdmOK Adm z) (hC : Reach A Adm C) (hn : 0 < n)
    {α : List (Ev n)} (hc : Crit z C α) : Biv z (run C α) [] := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hc.teams hA hAdm hC hn
  intro v
  have : ∃ r, SoloOut (run C α) r v := by
    cases v
    · exact ⟨p, hp.soloOut hA hAdm hC⟩
    · exact ⟨q, hq.soloOut hA hAdm hC⟩
  obtain ⟨r, k, hk⟩ := this
  exact ⟨solo r k, by simpa using InEs.of_crashFree (crashFree_replicate k r) z,
    by simpa using Dec.of_out hk⟩

/-- Steps of two processes on different objects commute. -/
lemma stepP_comm (E : Cfg A) {p q : Fin n} {i j : ι} (hpq : p ≠ q) (hij : i ≠ j)
    (hp : E.Poised p i) (hq : E.Poised q j) : (E.stepP p).stepP q = (E.stepP q).stepP p := by
  obtain ⟨o, k, ho⟩ := hp
  obtain ⟨o', k', ho'⟩ := hq
  have hq' : A.act ((E.stepP p).loc q) = .access j o' k' := by
    rw [stepP_loc_other E (Ne.symm hpq)]; exact ho'
  have hp' : A.act ((E.stepP q).loc p) = .access i o k := by
    rw [stepP_loc_other E hpq]; exact ho
  rw [stepP_of_access _ hq', stepP_of_access _ hp', stepP_of_access E ho, stepP_of_access E ho']
  simp only
  have m1 : Function.update E.mem i ((T i).δ (E.mem i) o).1 j = E.mem j :=
    Function.update_of_ne (Ne.symm hij) _ _
  have m2 : Function.update E.mem j ((T j).δ (E.mem j) o').1 i = E.mem i :=
    Function.update_of_ne hij _ _
  rw [m1, m2, Function.update_comm hpq, Function.update_comm hij]

/-- **Ovens' Lemma 9.** At a critical execution all processes are poised to apply an operation
to the same object. -/
theorem Crit.poised (hA : Solves A Adm) (hAdm : AdmOK Adm z) (hC : Reach A Adm C) (hn : 0 < n)
    {α : List (Ev n)} (hc : Crit z C α) : ∃ i, ∀ p, (run C α).Poised p i := by
  have hpo : ∀ p, ∃ i, (run C α).Poised p i := by
    intro p
    rcases h : A.act ((run C α).loc p) with ⟨i, o, k⟩ | v
    · exact ⟨i, o, k, h⟩
    · exact absurd h (hc.not_out hA hAdm hC p v)
  choose obj hobj using hpo
  have key : ∀ p q v, Team z C α p v → Team z C α q (!v) → obj p = obj q := by
    intro p q v hp hq
    by_contra hne
    have hpq : p ≠ q := by
      rintro rfl
      have := hp.unique hA hAdm hC hq
      cases v <;> simp at this
    have hs : InEs z (α ++ [.step p] ++ [.step q]) := by
      rw [List.append_assoc]; exact hc.1.append_crashFree (crashFree_steps [p, q])
    have hs' : InEs z (α ++ [.step q] ++ [.step p]) := by
      rw [List.append_assoc]; exact hc.1.append_crashFree (crashFree_steps [q, p])
    refine team_contra hA hAdm hC hp hq (r := p) hs hs' ?_
    have : run C (α ++ [.step p] ++ [.step q]) = run C (α ++ [.step q] ++ [.step p]) := by
      simp only [List.append_assoc, List.singleton_append, run_append, run_cons, run_nil,
        Cfg.next]
      exact stepP_comm _ hpq hne (hobj p) (hobj q)
    rw [this]
    exact AgreeOn.refl _ _
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hc.teams hA hAdm hC hn
  refine ⟨obj p, fun r => ?_⟩
  obtain ⟨w, hw⟩ := hc.team r
  have : obj r = obj p := by
    cases w
    · rw [key r q false hw hq, key p q false hp hq]
    · exact (key p r false hp hw).symm
  rw [← this]; exact hobj r

end Crit

/-! ## Univalence transfer (Ovens' Observation 5) -/

section Transfer

variable {Adm : List (Ev n) → Prop} {z : ℕ}

/-- **Ovens' Observation 5** (with the extra hypothesis, needed in general, that no process
outside `Q` is in an output state in `D'`): if `Q` is `v`-univalent in `γ` w.r.t. `E*_z(D)` and
`D'` is indistinguishable from `Dγ` to `Q` (with the same object values), then `Q` is
`v`-univalent in `D'` w.r.t. `E*_z(D')`. -/
lemma UnivQ.transfer {D D' : Cfg A} {Q : Set (Fin n)} {γ : List (Ev n)} {v : Bool}
    (h : UnivQ z D Q γ v) (hag : AgreeOn Q (run D γ) D') (hout : ∀ p ∉ Q, ∀ w, ¬ D'.Out p w) :
    UnivQ z D' Q [] v := by
  refine ⟨InEs.nil z, fun β hβ hs w hw => ?_⟩
  simp only [List.nil_append] at hs hw
  have hd : Dec (run D γ) β w := Dec.of_agreeOn hag hβ hout hw
  exact h.2 β hβ (h.1.append hs) w hd.of_suffix

lemma Univ.univQ {D : Cfg A} {γ : List (Ev n)} {v : Bool} (h : Univ z D γ v) (Q : Set (Fin n)) :
    UnivQ z D Q γ v := ⟨h.1, fun β _ hs w hw => h.2 β (fun _ _ => trivial) hs w hw⟩

/-- In a critical execution, a process of a set `Q` that is `v`-univalent is on team `v`. -/
lemma Crit.team_of_univQ (hA : Solves A Adm) (hAdm : AdmOK Adm z) {D : Cfg A}
    (hD : Reach A Adm D) {α : List (Ev n)} (hc : Crit z D α) {Q : Set (Fin n)} {v : Bool}
    (hQ : UnivQ z D Q α v) {r : Fin n} (hr : r ∈ Q) : Team z D α r v := by
  obtain ⟨w, hw⟩ := hc.team r
  have h1 := hw.soloOut hA hAdm hD
  have h2 := UnivQ.soloOut hA hAdm hD hQ hr
  rwa [h1.unique h2] at hw

end Transfer

/-! ## Object families -/

/-- The objects of an algorithm that uses read/write objects `R j` (`j : ιR`) and objects of type
`S` (indexed by `ιS`). -/
abbrev withRW {ιR ιS : Type} (R : ιR → ObjSpec) (S : ObjSpec) : ιR ⊕ ιS → ObjSpec :=
  Sum.elim R (fun _ => S)

/-! ## Counting accesses -/

/-- The object process `p` is poised to access in `C` (`none` if `p` is in an output state). -/
def objOf (C : Cfg A) (p : Fin n) : Option ι :=
  match A.act (C.loc p) with
  | .access i _ _ => some i
  | .out _ => none

/-- Number of operations applied by process `p` to object `i` in the execution `α` from `C`. -/
def accCount : Cfg A → List (Ev n) → Fin n → ι → ℕ
  | _, [], _, _ => 0
  | C, e :: α, p, i =>
    (if e = .step p ∧ objOf C p = some i then 1 else 0) + accCount (C.next e) α p i

/-- No accesses along the empty execution. -/
@[simp] lemma accCount_nil (C : Cfg A) (p : Fin n) (i : ι) : accCount C [] p i = 0 := rfl

/-- Unfolding `accCount` at the first event. -/
lemma accCount_cons (C : Cfg A) (e : Ev n) (α : List (Ev n)) (p : Fin n) (i : ι) :
    accCount C (e :: α) p i =
      (if e = .step p ∧ objOf C p = some i then 1 else 0) + accCount (C.next e) α p i := rfl

/-- Access counts are additive along concatenated executions. -/
lemma accCount_append (C : Cfg A) (α β : List (Ev n)) (p : Fin n) (i : ι) :
    accCount C (α ++ β) p i = accCount C α p i + accCount (run C α) β p i := by
  induction α generalizing C with
  | nil => simp
  | cons e α ih => simp only [List.cons_append, accCount_cons, ih, run_cons]; omega

/-- The access count of a single step. -/
lemma accCount_single (C : Cfg A) (p q : Fin n) (i : ι) :
    accCount C [.step p] q i = if q = p ∧ objOf C p = some i then 1 else 0 := by
  rw [accCount_cons, accCount_nil, Nat.add_zero]
  by_cases h : q = p
  · subst h; simp
  · have : (Ev.step p : Ev n) ≠ .step q := by simpa [eq_comm] using h
    simp [this, h]

/-! ## Persistence of outputs and invariants -/

/-- An output state persists along every execution in which its process does not crash. -/
lemma Cfg.Out.run {C : Cfg A} {p : Fin n} {v : Bool} (h : C.Out p v) {β : List (Ev n)}
    (hβ : Ev.crash p ∉ β) : (run C β).Out p v := by
  induction β generalizing C with
  | nil => exact h
  | cons e β ih =>
    rw [run_cons]
    refine ih ?_ (fun hm => hβ (List.mem_cons_of_mem _ hm))
    rcases e with q | q
    · by_cases hq : q = p
      · subst hq; simp only [Cfg.next, stepP_of_out C h]; exact h
      · unfold Cfg.Out; rw [next_loc_other C _ (by simpa [eq_comm] using hq)]; exact h
    · have hq : q ≠ p := by rintro rfl; exact hβ List.mem_cons_self
      unfold Cfg.Out; rw [next_loc_other C _ (by simpa [eq_comm] using hq)]; exact h

/-- A value decided in a crash-free execution is output at its end. -/
lemma Dec.exists_out {C : Cfg A} {α : List (Ev n)} {v : Bool} (h : Dec C α v)
    (hα : CrashFree α) : ∃ p, (run C α).Out p v := by
  obtain ⟨m, -, p, hp⟩ := h
  refine ⟨p, ?_⟩
  rw [← List.take_append_drop m α, run_append]
  exact hp.run (fun hm => hα p (List.mem_of_mem_drop hm))

/-- An invariant of configurations preserved by all steps holds along crash-free executions. -/
lemma inv_run_crashFree (Inv : Cfg A → Prop) (hstep : ∀ C p, Inv C → Inv (C.stepP p)) :
    ∀ (α : List (Ev n)) (C : Cfg A), Inv C → CrashFree α → Inv (run C α) := by
  intro α
  induction α with
  | nil => intro C h _; simpa using h
  | cons e α ih =>
    intro C hC hα
    rw [run_cons]
    apply ih _ _ (fun q hq => hα q (by simp [hq]))
    rcases e with q | q
    · exact hstep C q hC
    · exact absurd (by simp) (hα q)

/-! ## Progress -/

/-- All prefixes of an infinite execution are crash-free iff none of its events is a crash. -/
lemma pre_crashFree_iff (e : ℕ → Ev n) :
    (∀ t, CrashFree (pre e t)) ↔ ∀ t, ∀ p, e t ≠ .crash p := by
  constructor
  · intro h t p hp
    apply h (t + 1) p
    simp only [pre, List.mem_map, List.mem_range]
    exact ⟨t, by omega, hp⟩
  · intro h t p hp
    simp only [pre, List.mem_map, List.mem_range] at hp
    obtain ⟨t', -, ht'⟩ := hp
    exact h t' p ht'

/-- **Progress from a ranking function**: if every access strictly decreases a rank of the local
state, a process that takes infinitely many steps and does not crash after time `N` is in an
output state at some time `≥ N` (in any infinite execution from any configuration). This is the
progress condition of `Solves`, for any set of admissible executions. -/
theorem prog_of_rank (rank : A.L → ℕ)
    (hrank : ∀ l i o (κ : (T i).Resp → A.L) r, A.act l = .access i o κ → rank (κ r) < rank l)
    (C : Cfg A) (e : ℕ → Ev n) (p : Fin n) (N : ℕ) (hinf : ∀ M, ∃ t ≥ M, e t = .step p)
    (hN : ∀ t ≥ N, e t ≠ .crash p) : ∃ t ≥ N, ∃ v, (run C (pre e t)).Out p v := by
  set Cf : ℕ → Cfg A := fun t => run C (pre e t) with hCf
  have hsucc : ∀ t, Cf (t + 1) = (Cf t).next (e t) := by
    intro t; simp [hCf, pre_succ, run_concat]
  by_contra hno
  push Not at hno
  -- the rank of `p` along the execution
  set r : ℕ → ℕ := fun t => rank ((Cf t).loc p) with hr
  have hstepP : ∀ t ≥ N, rank (((Cf t).stepP p).loc p) < r t := by
    intro t ht
    rcases hact : A.act ((Cf t).loc p) with ⟨i, o, κ⟩ | v
    · rw [stepP_of_access _ hact]
      simpa [hr] using hrank _ i o κ _ hact
    · exact absurd hact (hno t ht v)
  have hle : ∀ t ≥ N, r (t + 1) ≤ r t := by
    intro t ht
    simp only [hr, hsucc]
    rcases he : e t with q | q
    · by_cases hq : q = p
      · subst hq; exact (hstepP t ht).le
      · rw [next_loc_other _ _ (by simpa using Ne.symm hq)]
    · have hq : q ≠ p := by rintro rfl; exact hN t ht he
      rw [next_loc_other _ _ (by simpa using Ne.symm hq)]
  have hmono : ∀ t ≥ N, ∀ d, r (t + d) ≤ r t := by
    intro t ht d
    induction d with
    | zero => simp
    | succ d ih => exact (hle (t + d) (by omega)).trans ih
  have key : ∀ j, ∃ t ≥ N, r t + j ≤ r N := by
    intro j
    induction j with
    | zero => exact ⟨N, le_rfl, by simp⟩
    | succ j ih =>
      obtain ⟨t, ht, hj⟩ := ih
      obtain ⟨t', ht', he⟩ := hinf t
      refine ⟨t' + 1, by omega, ?_⟩
      have h1 : r (t' + 1) < r t' := by
        simp only [hr, hsucc, he, Cfg.next]; exact hstepP t' (by omega)
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht'
      have h2 := hmono t ht d
      omega
  obtain ⟨t, -, ht⟩ := key (r N + 1)
  omega

/-! ## Wait-free consensus from an invariant -/

/-- **Wait-free consensus from an invariant.** If an invariant of the configurations reached from
the initial configuration with inputs `x` implies that all output values are the input of a
single process, and a rank strictly decreases at each access, the algorithm solves wait-free
consensus. -/
theorem wfConsensus_of_inv (Inv : (Fin n → Bool) → Cfg A → Prop)
    (hinit : ∀ x, Inv x (initCfg A x))
    (hstep : ∀ x C p, Inv x C → Inv x (C.stepP p))
    (hout : ∀ x C, Inv x C → ∃ q, ∀ p w, C.Out p w → w = x q)
    (rank : A.L → ℕ)
    (hrank : ∀ l i o (κ : (T i).Resp → A.L) r, A.act l = .access i o κ → rank (κ r) < rank l) :
    WFConsensus A := by
  have reach : ∀ x (α : List (Ev n)), CrashFree α → Inv x (run (initCfg A x) α) :=
    fun x α hα => inv_run_crashFree (Inv x) (hstep x) α _ (hinit x) hα
  refine ⟨?_, ?_, ?_⟩
  · intro x γ hγ v w hv hw
    obtain ⟨p, hp⟩ := hv.exists_out hγ
    obtain ⟨p', hp'⟩ := hw.exists_out hγ
    obtain ⟨q, hq⟩ := hout x _ (reach x γ hγ)
    rw [hq p v hp, hq p' w hp']
  · intro x γ hγ v hv
    obtain ⟨p, hp⟩ := hv.exists_out hγ
    obtain ⟨q, hq⟩ := hout x _ (reach x γ hγ)
    exact ⟨q, (hq p v hp).symm⟩
  · intro x e p N _ hinf hN
    exact prog_of_rank rank hrank _ e p N hinf hN

end Cslib.SharedMemory.Recoverable
