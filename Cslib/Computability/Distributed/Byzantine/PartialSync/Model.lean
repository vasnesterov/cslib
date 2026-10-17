/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.ENat.Lattice
public import Cslib.Foundations.Data.List.Basic

/-!
# A partially synchronous Byzantine message-passing model

A discrete-time, deterministic model of `n = Fintype.card P` processes communicating over
authenticated point-to-point links, in the partially synchronous model of Dwork, Lynch and
Stockmeyer [DworkLynchStockmeyer1988]: there is a (per-run, unknown to the processes) global
stabilization time `gst`, and messages between correct processes sent at time `τ` are delivered by
`max τ gst + δ` (`δ` is a model parameter, known to the algorithm designer).

## Shape of the model

* An `Algorithm` is a family of deterministic state machines (one per process). At every time
  `τ ∈ ℕ` every correct process
  1. sends `send p (st τ p) q : List M` to every process `q`,
  2. receives `inbox p τ : P → List M` (from each sender, the batches delivered at time `τ`),
  3. moves to `st (τ+1) p = step p (st τ p) (inbox p τ)`.
  Its decision is read off its state: `decide p (st τ p) : Option VO`.
* A `Run` is the *adversary's choice*: the set of faulty processes, the inputs (proposals),
  the GST, what every faulty process sends (arbitrary, `byz`), and the delivery time `dl q τ p` of
  the batch of messages sent by `q` at time `τ` to `p`. The states of the correct processes are
  then *computed* (`Run.st`) by recursion on time. A batch delivered "in the past"
  (`dl q τ p < τ`) is lost; `Run.Valid` forbids this for correct-to-correct links.
* `Run.Valid t δ` imposes the model constraints: at most `t` faulty processes, and every batch
  between correct processes sent at `τ` is delivered at a time in `[τ, max τ gst + δ]`.

Since every run is infinite and the adversary is a fixed (oblivious) object, executions in the
sense of "finite prefixes + continuations" are expressed via agreement of runs up to a time `T`.
The key tool is `Run.st_eq_of_inbox_eq`: two runs that feed a set `X` of processes the same
inboxes up to time `T` (given that `X` behaved identically so far) give `X` the same states;
this is the formal *indistinguishability* principle used for all "merge executions" and
"delay a group's messages" arguments.
On a link with a constant delay `e`, the inbox at time `τ` is the batch sent at time `τ - e`
(`Run.inbox_of_dl_eq_add`).

## Scope of results proved in this model

**Correct processes are drift-free and awake from time `0`.** Every correct process takes a step
at every time unit from time `0` on, so local step counters are perfectly synchronized clocks.
This, and the other modelling choices below, make the adversary *weaker* than in the textbook
partially synchronous model (with clock drift and processes that may start late). Hence:

* **impossibility results and lower bounds** proved here are *stronger* than their textbook
  counterparts (they hold even against this weaker adversary);
* **possibility results** (protocols verified in this model) are *weaker*: they hold in this
  model only, and transferring them to a model with drift or late wake-up requires an additional
  (view-)synchronizer argument.

## Modelling choices

* Correct processes take a step at every time unit and start at time `0` (≤ GST); in particular
  their local clocks never drift (they can count steps). Before GST the adversary can still make
  a process "look asleep" to everyone else by delaying all its messages.
* All messages of one batch (same sender, time and destination) are delivered together.
* No signatures: faulty processes may send arbitrary messages (but cannot forge the sender
  identity, as `inbox` is indexed by the sender).
* Lock-step synchronous rounds are the special case `gst = 0`, `δ = 0` (then every message sent
  at `τ` is processed in the step at `τ`).

## Related models in CSLib

* `Cslib.Byzantine.LockStep` is a synchronous lock-step model with history-based protocols on an
  arbitrary communication graph (with omissions). It is related to this model by
  `Cslib.Byzantine.LockStep.toAlgorithm_st`: a lock-step protocol, compiled into an `Algorithm`,
  behaves in the runs of this model with `gst = 0` and `δ = 0` exactly as in the lock-step model.
* `Cslib.FLP` models *asynchronous* crash-prone consensus as a labelled transition system with
  fairness, where processes may be scheduled arbitrarily; here time is discrete and global, and
  faults are Byzantine. The asynchronous model corresponds informally to an infinite GST, which
  this model does not allow (every run has a finite `gst`).

## References

* [C. Dwork, N. Lynch, L. Stockmeyer, *Consensus in the presence of partial
  synchrony*][DworkLynchStockmeyer1988]
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

/-- A deterministic distributed algorithm: one state machine per process.
`P` processes, `M` message contents, `S` local states, `VI` proposals, `VO` decisions. -/
structure Algorithm (P M S VI VO : Type*) where
  /-- Initial state of process `p` with proposal `v`. -/
  init : P → VI → S
  /-- State transition, given the messages received at this time step from each sender. -/
  step : P → S → (P → List M) → S
  /-- Messages sent by process `p` in state `s` to process `q`. -/
  send : P → S → P → List M
  /-- The decision (if any) exhibited by the state. -/
  decide : P → S → Option VO

/-- The adversary's choices, which determine a run of any algorithm. -/
structure Run (P M VI : Type*) where
  /-- The faulty (Byzantine) processes. -/
  faulty : Finset P
  /-- The proposals (only relevant for correct processes). -/
  inp : P → VI
  /-- Global stabilization time. -/
  gst : ℕ
  /-- `byz q τ p`: messages sent by the faulty process `q` at time `τ` to `p`. -/
  byz : P → ℕ → P → List M
  /-- `dl q τ p`: time at which the batch sent by `q` at time `τ` to `p` is delivered. -/
  dl : P → ℕ → P → ℕ

namespace Run

variable {P M S VI VO : Type*} [DecidableEq P]
variable (A : Algorithm P M S VI VO) (R : Run P M VI)

/-- Messages sent by `q` at time `τ` to `p`, given a (partial) history `h` of states. -/
def outWith (h : ℕ → P → S) (q : P) (τ : ℕ) (p : P) : List M :=
  if q ∈ R.faulty then R.byz q τ p else A.send q (h τ q) p

/-- Messages received by `p` at time `τ` from `q`, given a (partial) history `h` of states. -/
def inboxWith (h : ℕ → P → S) (p : P) (τ : ℕ) (q : P) : List M :=
  (List.range (τ + 1)).flatMap fun τ' => if R.dl q τ' p = τ then R.outWith A h q τ' p else []

/-- `stUpTo τ` is the history of states, correct at all times `≤ τ`. -/
def stUpTo : ℕ → ℕ → P → S
  | 0 => fun _ p => A.init p (R.inp p)
  | τ + 1 => fun σ p =>
      if σ ≤ τ then stUpTo τ σ p
      else A.step p (stUpTo τ τ p) (R.inboxWith A (stUpTo τ) p τ)

/-- The local state of process `p` at (the beginning of) time `τ`. Meaningful for correct `p`. -/
def st (τ : ℕ) (p : P) : S := R.stUpTo A τ τ p

/-- Messages sent by `q` at time `τ` to `p`. -/
def out (q : P) (τ : ℕ) (p : P) : List M := R.outWith A (R.st A) q τ p

/-- Messages received by `p` at time `τ` from `q`. -/
def inbox (p : P) (τ : ℕ) (q : P) : List M := R.inboxWith A (R.st A) p τ q

/-- The batch sent by `q` at time `τ'` to `p`, if it is delivered at time `τ` (else `[]`). -/
def dlv (q : P) (τ' : ℕ) (p : P) (τ : ℕ) : List M :=
  if R.dl q τ' p = τ then R.out A q τ' p else []

theorem stUpTo_eq_of_le {τ σ : ℕ} (h : σ ≤ τ) : R.stUpTo A τ σ = R.stUpTo A σ σ := by
  induction τ with
  | zero => obtain rfl : σ = 0 := by omega
            rfl
  | succ τ ih =>
    rcases Nat.lt_or_ge σ (τ + 1) with h' | h'
    · funext p
      simp only [stUpTo, show σ ≤ τ by omega, ite_true]
      rw [ih (by omega)]
    · obtain rfl : σ = τ + 1 := by omega
      rfl

@[simp] theorem st_zero (p : P) : R.st A 0 p = A.init p (R.inp p) := rfl

theorem inboxWith_congr {h h' : ℕ → P → S} {τ : ℕ} (hh : ∀ σ ≤ τ, h σ = h' σ) (p q : P) :
    R.inboxWith A h p τ q = R.inboxWith A h' p τ q := by
  unfold inboxWith outWith
  refine List.flatMap_congr fun τ' hτ' => ?_
  have : τ' ≤ τ := by simp at hτ'; omega
  rw [hh τ' this]

theorem st_succ (τ : ℕ) (p : P) :
    R.st A (τ + 1) p = A.step p (R.st A τ p) (R.inbox A p τ) := by
  change R.stUpTo A (τ + 1) (τ + 1) p = _
  simp only [stUpTo, show ¬ τ + 1 ≤ τ by omega, ite_false]
  congr 1
  funext q
  exact R.inboxWith_congr A (fun σ hσ => R.stUpTo_eq_of_le A hσ) p q

theorem out_of_faulty {q : P} (hq : q ∈ R.faulty) (τ : ℕ) (p : P) :
    R.out A q τ p = R.byz q τ p := by
  simp [out, outWith, hq]

theorem out_of_correct {q : P} (hq : q ∉ R.faulty) (τ : ℕ) (p : P) :
    R.out A q τ p = A.send q (R.st A τ q) p := by
  simp [out, outWith, hq]

theorem inbox_eq_flatMap (p : P) (τ : ℕ) (q : P) :
    R.inbox A p τ q = (List.range (τ + 1)).flatMap fun τ' => R.dlv A q τ' p τ := rfl

/-- Two runs give `p` the same inbox at time `τ` if every batch delivered to `p` at time `τ`
coincides. -/
theorem inbox_eq_of_dlv_eq {R' : Run P M VI} {p : P} {τ : ℕ}
    (h : ∀ q, ∀ τ' ≤ τ, R.dlv A q τ' p τ = R'.dlv A q τ' p τ) :
    R.inbox A p τ = R'.inbox A p τ := by
  funext q
  rw [inbox_eq_flatMap, inbox_eq_flatMap]
  refine List.flatMap_congr fun τ' hτ' => h q τ' ?_
  simp at hτ'; omega

theorem dlv_eq_nil_of_ne {q : P} {τ' : ℕ} {p : P} {τ : ℕ} (h : R.dl q τ' p ≠ τ) :
    R.dlv A q τ' p τ = [] := by simp [dlv, h]

/-- **Indistinguishability principle.** Let `X` be a set of processes, each `p ∈ X` correct in
`R` and in a reference run `ref p`, with the same proposal. If, as long as all processes of `X`
had the same states in `R` as in their reference runs, they also get the same inboxes, then they
have the same states up to time `T`. -/
theorem st_eq_of_inbox_eq {ref : P → Run P M VI} {X : Set P} {T : ℕ}
    (hX : ∀ p ∈ X, R.inp p = (ref p).inp p)
    (hin : ∀ τ < T, (∀ r ∈ X, ∀ σ ≤ τ, R.st A σ r = (ref r).st A σ r) →
      ∀ p ∈ X, R.inbox A p τ = (ref p).inbox A p τ) :
    ∀ τ ≤ T, ∀ p ∈ X, R.st A τ p = (ref p).st A τ p := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro hτ p hp
    rcases τ with _ | τ
    · simp [hX p hp]
    · rw [st_succ, st_succ, ih τ (by omega) (by omega) p hp,
        hin τ (by omega) (fun r hr σ hσ => ih σ (by omega) (by omega) r hr) p hp]

/-- Runs depend only on `init`, `step` and `send`, not on the decision map. -/
theorem stUpTo_congr {VO' : Type*} {A' : Algorithm P M S VI VO'} (hi : A.init = A'.init)
    (hs : A.step = A'.step) (hm : A.send = A'.send) (τ : ℕ) :
    R.stUpTo A τ = R.stUpTo A' τ := by
  induction τ with
  | zero => funext σ p; simp [stUpTo, hi]
  | succ τ ih =>
    funext σ p
    simp only [stUpTo, ih, hs]
    congr 2
    funext q
    simp [inboxWith, outWith, hm]

theorem st_congr {VO' : Type*} {A' : Algorithm P M S VI VO'} (hi : A.init = A'.init)
    (hs : A.step = A'.step) (hm : A.send = A'.send) : R.st A = R.st A' := by
  funext τ p; simp [st, R.stUpTo_congr A hi hs hm]

theorem out_congr {VO' : Type*} {A' : Algorithm P M S VI VO'} (hi : A.init = A'.init)
    (hs : A.step = A'.step) (hm : A.send = A'.send) : R.out A = R.out A' := by
  funext q τ p; simp [out, outWith, R.st_congr A hi hs hm, hm]

/-- Model constraints of the partially synchronous model with at most `t` faults and
post-GST delay bound `δ`. -/
structure Valid (t δ : ℕ) (R : Run P M VI) : Prop where
  card_faulty : R.faulty.card ≤ t
  dl_ge : ∀ q τ p, q ∉ R.faulty → p ∉ R.faulty → τ ≤ R.dl q τ p
  dl_le : ∀ q τ p, q ∉ R.faulty → p ∉ R.faulty → R.dl q τ p ≤ max τ R.gst + δ

/-- A run is *canonical* if faulty processes never send anything. -/
def Canonical (R : Run P M VI) : Prop := ∀ q ∈ R.faulty, ∀ τ p, R.byz q τ p = []

theorem out_eq_nil_of_canonical {R : Run P M VI} (hR : R.Canonical) {q : P} (hq : q ∈ R.faulty)
    (τ : ℕ) (p : P) : R.out A q τ p = [] := by
  rw [out_of_faulty A R hq, hR q hq]

/-- `p` decides `v` at some time. -/
def Decides (p : P) (v : VO) : Prop := ∃ τ, A.decide p (R.st A τ p) = some v

/-- Number of messages sent by correct processes at time `τ` to *other* processes (messages a
process sends to itself are local computation and are not counted). -/
def msgsAt [Fintype P] (τ : ℕ) : ℕ :=
  ∑ q ∈ Finset.univ.filter (· ∉ R.faulty), ∑ p ∈ Finset.univ.filter (· ≠ q), (R.out A q τ p).length

/-- Number of messages sent by correct processes during `[gst, N)`. -/
def msgsUpTo [Fintype P] (N : ℕ) : ℕ := ∑ τ ∈ Finset.Ico R.gst N, R.msgsAt A τ

/-- Message complexity of a run: number of messages sent by correct processes during
`[gst, ∞)`. -/
noncomputable def msgComplexity [Fintype P] : ℕ∞ := ⨆ N, (R.msgsUpTo A N : ℕ∞)

/-- On a link `q → p` on which every batch is delivered `e` time units after it is sent, the inbox
of `p` at time `τ` is the batch sent by `q` at time `τ - e` (nothing before time `e`). -/
theorem inbox_of_dl_eq_add {R : Run P M VI} {q p : P} {e : ℕ} (h : ∀ σ, R.dl q σ p = σ + e)
    (τ : ℕ) : R.inbox A p τ q = if e ≤ τ then R.out A q (τ - e) p else [] := by
  rw [inbox_eq_flatMap]
  split_ifs with he
  · rw [List.flatMap_range_eq_of_forall_ne (k := τ - e) (by omega)]
    · simp only [dlv, h]; rw [ite_eq_left (by omega)]
    · intro t ht
      simp only [dlv, h]; rw [ite_eq_right (by omega)]
  · refine List.flatMap_eq_nil_iff.mpr fun t _ => ?_
    simp only [dlv, h]
    rw [ite_eq_right (by omega)]

end Run

end Cslib.Byzantine.PartialSync
