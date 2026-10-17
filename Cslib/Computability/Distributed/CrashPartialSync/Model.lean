/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Fintype.Card

/-!
# Crash-prone partially synchronous message passing

A discrete-time model of `n = Fintype.card P` deterministic processes that may **crash**,
communicating over point-to-point links in the partially synchronous model of Dwork, Lynch and
Stockmeyer, as used by Ryabinin, Gotsman and Sutra [RyabininGotsmanSutra2025] (§2). One time unit
is the known message delay bound `Δ`.

## Shape

* A `Protocol` is a family of deterministic state machines. At every time `τ` at which it is alive,
  process `p`
  1. receives the list `inbox p τ` of the messages delivered at time `τ` (pairs sender/message),
     in an order chosen by the adversary, and possibly an invocation `inv p τ : Option V`
     (for a consensus *task* this is the input at time `0`; for a consensus *object* it is a call
     `propose(v)`),
  2. moves to `st (τ + 1) p = step p τ (st τ p) (inv p τ) (inbox p τ)` (it knows the time `τ`:
     clocks are synchronized),
  3. sends `send p (st (τ + 1) p) q` to every `q` (these messages are *sent at time `τ`*).
  Its current decision (output) is `decide p (st τ p)`.
* A `Run` is the adversary's choice only: crash times (`crash p = some c`: `p` takes its steps at
  the times `τ < c` and none afterwards; `none`: `p` is correct), the GST, the invocations, the
  delivery time `dl q τ p` of the batch of messages sent by `q` at time `τ` to `p` (a batch with
  `dl q τ p ≤ τ` is lost) and the order `ord p τ` in which a process gets the messages delivered to
  it at time `τ`. States are computed (`Run.st`).
* `Run.Valid f`: at most `f` processes crash, `ord` only permutes, and links between *correct*
  processes are reliable and timely after GST: a batch sent at `τ` arrives in
  `[τ + 1, max τ gst + 1]`. Messages from or to faulty processes may be lost (reliable links
  connect correct processes; a process that crashes may lose the messages still in transit).
* `Run.st_eq_of_inbox_eq` is the indistinguishability principle: processes that get the same
  invocations and inboxes as in reference runs have the same states.
* `Run.mem_inbox`: the messages delivered to `x` at time `τ` are exactly those sent at some
  `τ' < τ` with delivery time `τ`; `Run.mem_inbox_of_gst`: after GST, a message between correct
  processes sent at `τ` is delivered at `τ + 1`.
* `Run.invariant` is the induction principle for system invariants (a state invariant `SI` and a
  message invariant `MI` indexed by the sending time), with `Run.invariant_st`,
  `Run.invariant_out`, `Run.invariant_inbox`; `Run.st_mono`: a property preserved by every step
  of a process persists.
* `syncRun E inv ord` is the `E`-faulty synchronous run: the processes of `E` crash at time `0`,
  the others are correct, and every message is delivered one time unit after it is sent.

Since the delivery order inside a time step is chosen by the adversary, statements of the form
"there exists an `E`-faulty synchronous run" quantify over this order (in models with
instantaneous local computation, simultaneous deliveries happen in some order).

## Related models in CSLib

* `Cslib.Byzantine.PartialSync` is a partially synchronous model with *Byzantine* faults, inputs
  only at time `0`, per-sender inboxes and sends before the step. This model has *crash* faults,
  invocations at any time (so that it covers shared objects such as a consensus object as well
  as tasks), adversarially ordered inboxes and crash times, which the good-case latency
  arguments for crash-tolerant protocols need. The two models are not formally related.
* `Cslib.AsyncMP` and `Cslib.FLP` are *asynchronous* crash-prone models; here every run has a
  finite GST.

## References

* [F. Ryabinin, A. Gotsman, P. Sutra, *Revisiting lower bounds for two-step
  consensus*][RyabininGotsmanSutra2025]
-/

@[expose] public section

namespace Cslib.CrashPartialSync

open Finset

/-- A deterministic distributed protocol (one state machine per process); `V` values, `M` messages,
`S` local states. -/
structure Protocol (P V M S : Type*) where
  /-- Initial state. -/
  init : P → S
  /-- Transition at time `τ`, given the invocation (if any) and the ordered list of messages
  (sender, content) delivered at this time. -/
  step : P → ℕ → S → Option V → List (P × M) → S
  /-- Messages sent by `p` in (post-step) state `s` to `q`. -/
  send : P → S → P → List M
  /-- The decision exhibited by the state. -/
  decide : P → S → Option V

/-- The adversary's choices, which determine a run of any protocol. -/
structure Run (P V M : Type*) where
  /-- Crash time (`none`: correct). A process with `crash p = some c` takes steps at `τ < c`. -/
  crash : P → Option ℕ
  /-- Global stabilization time. -/
  gst : ℕ
  /-- Invocations (inputs / calls to `propose`). -/
  inv : P → ℕ → Option V
  /-- `dl q τ p`: delivery time of the batch sent by `q` at time `τ` to `p` (lost if `≤ τ`). -/
  dl : P → ℕ → P → ℕ
  /-- Order in which `p` processes the messages delivered at time `τ`. -/
  ord : P → ℕ → List (P × M) → List (P × M)

/-- `ord` only reorders the delivered messages. -/
def IsOrder {P M : Type*} (ord : P → ℕ → List (P × M) → List (P × M)) : Prop :=
  ∀ x τ l, (ord x τ l).Perm l

theorem IsOrder.id {P M : Type*} : IsOrder (fun (_ : P) (_ : ℕ) (l : List (P × M)) => l) :=
  fun _ _ _ => List.Perm.refl _

theorem IsOrder.nil {P M : Type*} {ord : P → ℕ → List (P × M) → List (P × M)} (h : IsOrder ord)
    (x : P) (τ : ℕ) : ord x τ [] = [] :=
  List.Perm.nil_eq (h x τ []).symm |>.symm

namespace Run

variable {P V M S : Type*}
variable (A : Protocol P V M S) (R : Run P V M)

/-- `p` takes a step at time `τ`. -/
def alive (p : P) (τ : ℕ) : Bool := (R.crash p).all fun c => decide (τ < c)

theorem alive_iff {p : P} {τ : ℕ} : R.alive p τ ↔ ∀ c, R.crash p = some c → τ < c := by
  unfold alive; cases R.crash p <;> simp

theorem alive_of_crash_none {p : P} (h : R.crash p = none) (τ : ℕ) : R.alive p τ := by
  simp [alive, h]

/-- Messages sent by `q` at time `τ` to `x`, given a (partial) history `h` of states. -/
def outWith (h : ℕ → P → S) (q : P) (τ : ℕ) (x : P) : List M :=
  if R.alive q τ then A.send q (h (τ + 1) q) x else []

variable [Fintype P]

/-- Messages delivered to `x` at time `τ` in canonical order (by send time, then sender). -/
noncomputable def canonWith (h : ℕ → P → S) (x : P) (τ : ℕ) : List (P × M) :=
  (List.range τ).flatMap fun τ' => (Finset.univ : Finset P).toList.flatMap fun q =>
    if R.dl q τ' x = τ then (R.outWith A h q τ' x).map (Prod.mk q) else []

/-- `stUpTo τ` is a history of states, correct at all times `≤ τ`. -/
noncomputable def stUpTo : ℕ → ℕ → P → S
  | 0 => fun _ p => A.init p
  | τ + 1 => fun σ p =>
      if σ ≤ τ then stUpTo τ σ p
      else if R.alive p τ then
        A.step p τ (stUpTo τ τ p) (R.inv p τ) (R.ord p τ (R.canonWith A (stUpTo τ) p τ))
      else stUpTo τ τ p

/-- The local state of `p` at time `τ` (before its step at time `τ`). -/
noncomputable def st (τ : ℕ) (p : P) : S := R.stUpTo A τ τ p

/-- Messages sent by `q` at time `τ` to `x`. -/
noncomputable def out (q : P) (τ : ℕ) (x : P) : List M := R.outWith A (R.st A) q τ x

/-- The batch sent by `q` at time `τ'` to `x`, if it is delivered at time `τ` (else `[]`). -/
noncomputable def dlv (q : P) (τ' : ℕ) (x : P) (τ : ℕ) : List M :=
  if R.dl q τ' x = τ then R.out A q τ' x else []

/-- Messages delivered to `x` at time `τ`, in canonical order. -/
noncomputable def canon (x : P) (τ : ℕ) : List (P × M) := R.canonWith A (R.st A) x τ

/-- Messages delivered to `x` at time `τ`, in the order in which `x` processes them. -/
noncomputable def inbox (x : P) (τ : ℕ) : List (P × M) := R.ord x τ (R.canon A x τ)

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

@[simp] theorem st_zero (p : P) : R.st A 0 p = A.init p := rfl

theorem canonWith_congr {h h' : ℕ → P → S} {τ : ℕ} (hh : ∀ σ ≤ τ, h σ = h' σ) (x : P) :
    R.canonWith A h x τ = R.canonWith A h' x τ := by
  unfold canonWith outWith
  refine List.flatMap_congr fun τ' hτ' => List.flatMap_congr fun q _ => ?_
  have : τ' + 1 ≤ τ := by simp at hτ'; omega
  rw [hh (τ' + 1) this]

theorem st_succ (τ : ℕ) (p : P) :
    R.st A (τ + 1) p =
      if R.alive p τ then A.step p τ (R.st A τ p) (R.inv p τ) (R.inbox A p τ) else R.st A τ p := by
  change R.stUpTo A (τ + 1) (τ + 1) p = _
  simp only [stUpTo, show ¬ τ + 1 ≤ τ by omega, ite_false]
  congr 2
  unfold inbox canon
  congr 1
  exact R.canonWith_congr A (fun σ hσ => R.stUpTo_eq_of_le A hσ) p

theorem st_succ_of_alive {τ : ℕ} {p : P} (h : R.alive p τ) :
    R.st A (τ + 1) p = A.step p τ (R.st A τ p) (R.inv p τ) (R.inbox A p τ) := by
  rw [st_succ, ite_eq_left h]

theorem st_succ_of_not_alive {τ : ℕ} {p : P} (h : R.alive p τ = false) :
    R.st A (τ + 1) p = R.st A τ p := by
  rw [st_succ, ite_eq_right (by simp [h])]

/-- A process that crashes at time `0` stays in its initial state. -/
theorem st_of_crash_zero {p : P} (h : R.crash p = some 0) (τ : ℕ) : R.st A τ p = A.init p := by
  induction τ with
  | zero => rfl
  | succ τ ih => rw [st_succ_of_not_alive A R (by simp [alive, h]), ih]

theorem out_of_alive {q : P} {τ : ℕ} (h : R.alive q τ) (x : P) :
    R.out A q τ x = A.send q (R.st A (τ + 1) q) x := by
  simp [out, outWith, h]

theorem out_of_not_alive {q : P} {τ : ℕ} (h : R.alive q τ = false) (x : P) :
    R.out A q τ x = [] := by
  simp [out, outWith, h]

theorem canon_eq_flatMap (x : P) (τ : ℕ) :
    R.canon A x τ = (List.range τ).flatMap fun τ' => (Finset.univ : Finset P).toList.flatMap
      fun q => (R.dlv A q τ' x τ).map (Prod.mk q) := by
  unfold canon canonWith dlv
  refine List.flatMap_congr fun τ' _ => List.flatMap_congr fun q _ => ?_
  split_ifs <;> rfl

theorem canon_zero (x : P) : R.canon A x 0 = [] := by
  simp [canon_eq_flatMap]

/-- Two runs deliver the same messages to `x` at time `τ` if every batch coincides. -/
theorem canon_eq_of_dlv_eq {R' : Run P V M} {x : P} {τ : ℕ}
    (h : ∀ q, ∀ τ' < τ, R.dlv A q τ' x τ = R'.dlv A q τ' x τ) :
    R.canon A x τ = R'.canon A x τ := by
  rw [canon_eq_flatMap, canon_eq_flatMap]
  refine List.flatMap_congr fun τ' hτ' => List.flatMap_congr fun q _ => ?_
  rw [h q τ' (by simpa using hτ')]

theorem inbox_eq_of_dlv_eq {R' : Run P V M} {x : P} {τ : ℕ} (ho : R.ord x τ = R'.ord x τ)
    (h : ∀ q, ∀ τ' < τ, R.dlv A q τ' x τ = R'.dlv A q τ' x τ) :
    R.inbox A x τ = R'.inbox A x τ := by
  unfold inbox; rw [ho, R.canon_eq_of_dlv_eq A h]

theorem dlv_eq_nil_of_ne {q : P} {τ' : ℕ} {x : P} {τ : ℕ} (h : R.dl q τ' x ≠ τ) :
    R.dlv A q τ' x τ = [] := by simp [dlv, h]

theorem dlv_of_eq {q : P} {τ' : ℕ} {x : P} {τ : ℕ} (h : R.dl q τ' x = τ) :
    R.dlv A q τ' x τ = R.out A q τ' x := by simp [dlv, h]

/-- **Indistinguishability principle.** Let `X` be a set of processes, each `p ∈ X` compared with
a reference run `ref p`. If the processes of `X` are alive at the same times and get the same
invocations, and — as long as all processes of `X` had the same states as in their reference
runs — they also get the same inboxes, then they have the same states up to time `T`. -/
theorem st_eq_of_inbox_eq {ref : P → Run P V M} {X : Set P} {T : ℕ}
    (hal : ∀ p ∈ X, ∀ τ < T, R.alive p τ = (ref p).alive p τ)
    (hinv : ∀ p ∈ X, ∀ τ < T, R.alive p τ → R.inv p τ = (ref p).inv p τ)
    (hin : ∀ τ < T, (∀ r ∈ X, ∀ σ ≤ τ, R.st A σ r = (ref r).st A σ r) →
      ∀ p ∈ X, R.alive p τ → R.inbox A p τ = (ref p).inbox A p τ) :
    ∀ τ ≤ T, ∀ p ∈ X, R.st A τ p = (ref p).st A τ p := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro hτ p hp
    rcases τ with _ | τ
    · rfl
    · have IH : ∀ r ∈ X, ∀ σ ≤ τ, R.st A σ r = (ref r).st A σ r :=
        fun r hr σ hσ => ih σ (by omega) (by omega) r hr
      rw [st_succ, st_succ, ← hal p hp τ (by omega), IH p hp τ le_rfl]
      by_cases h : R.alive p τ
      · rw [ite_eq_left h, ite_eq_left h, hinv p hp τ (by omega) h, hin τ (by omega) IH p hp h]
      · rw [ite_eq_right h, ite_eq_right h]

/-- Runs depend only on `init`, `step` and `send`. -/
theorem st_congr {A' : Protocol P V M S} (hi : A.init = A'.init) (hs : A.step = A'.step)
    (hm : A.send = A'.send) : R.st A = R.st A' := by
  have : ∀ τ, R.stUpTo A τ = R.stUpTo A' τ := by
    intro τ
    induction τ with
    | zero => funext σ p; simp [stUpTo, hi]
    | succ τ ih =>
      funext σ p
      simp only [stUpTo, ih, hs]
      congr 4
      unfold canonWith outWith
      simp [hm]
  funext τ p; simp [st, this]

/-- The faulty processes (those that crash at some time). -/
def faulty : Finset P := Finset.univ.filter fun p => R.crash p ≠ none

/-- Model constraints: at most `f` crashes, `ord` permutes, and links between correct processes
are reliable, with delay at most one time unit after GST. -/
structure Valid (f : ℕ) (R : Run P V M) : Prop where
  card_faulty : R.faulty.card ≤ f
  ord_perm : IsOrder R.ord
  dl_ge : ∀ q τ x, R.crash q = none → R.crash x = none → τ + 1 ≤ R.dl q τ x
  dl_le : ∀ q τ x, R.crash q = none → R.crash x = none → R.dl q τ x ≤ max τ R.gst + 1

/-- `p` exhibits decision `v` at time `τ`. -/
def DecidesAt (p : P) (τ : ℕ) (v : V) : Prop := A.decide p (R.st A τ p) = some v

/-- `p` *returns* `v` at time `τ`: it exhibits the decision `v` at `τ`, after an invocation. -/
def RespondsAt (p : P) (τ : ℕ) (v : V) : Prop :=
  (∃ τ₀ < τ, R.inv p τ₀ ≠ none) ∧ R.DecidesAt A p τ v

/-- Every process invokes `propose` at most once. -/
def WellFormed : Prop := ∀ p τ τ', R.inv p τ ≠ none → R.inv p τ' ≠ none → τ = τ'

/-! ### Inboxes and invariants -/

/-- Membership in the canonically ordered list of deliveries. -/
theorem mem_canon {x : P} {τ : ℕ} {q : P} {m : M} :
    (q, m) ∈ R.canon A x τ ↔ ∃ τ' < τ, R.dl q τ' x = τ ∧ m ∈ R.out A q τ' x := by
  rw [canon_eq_flatMap]
  simp only [List.mem_flatMap, List.mem_range, Finset.mem_toList, Finset.mem_univ, true_and,
    List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨τ', hτ', q', ⟨m', hm', rfl, rfl⟩⟩
    unfold dlv at hm'
    split_ifs at hm' with h
    · exact ⟨τ', hτ', h, hm'⟩
    · simp at hm'
  · rintro ⟨τ', hτ', hd, hm⟩
    exact ⟨τ', hτ', q, m, by simpa [dlv, hd] using hm, rfl, rfl⟩

/-- The messages delivered to `x` at time `τ` are exactly those sent at some `τ' < τ` with
delivery time `τ`. -/
theorem mem_inbox (hR : IsOrder R.ord) {x : P} {τ : ℕ} {q : P} {m : M} :
    (q, m) ∈ R.inbox A x τ ↔ ∃ τ' < τ, R.dl q τ' x = τ ∧ m ∈ R.out A q τ' x := by
  unfold inbox
  rw [(hR x τ _).mem_iff, mem_canon]

/-- After GST, a message between correct processes sent at `τ` is delivered at `τ + 1`. -/
theorem mem_inbox_of_gst {f : ℕ} (hR : R.Valid f) {q x : P} (hq : R.crash q = none)
    (hx : R.crash x = none) {τ : ℕ} (hτ : R.gst ≤ τ) {m : M} (hm : m ∈ R.out A q τ x) :
    (q, m) ∈ R.inbox A x (τ + 1) := by
  rw [mem_inbox A R hR.ord_perm]
  refine ⟨τ, by omega, ?_, hm⟩
  have h1 := hR.dl_ge q τ x hq hx
  have h2 := hR.dl_le q τ x hq hx
  rw [max_eq_left hτ] at h2
  omega

/-- **Invariant principle.** A state invariant `SI τ p` (for the state of `p` at time `τ`) and a
message invariant `MI τ q` (for the messages sent by `q` at time `τ`), established by every step,
hold throughout the run. -/
theorem invariant (hR : IsOrder R.ord) (SI : ℕ → P → S → Prop) (MI : ℕ → P → M → Prop)
    (h0 : ∀ p, SI 0 p (A.init p))
    (hmono : ∀ τ p s, SI τ p s → SI (τ + 1) p s)
    (hstep : ∀ τ p, R.alive p τ → SI τ p (R.st A τ p) →
      (∀ q m, (q, m) ∈ R.inbox A p τ → ∃ τ' < τ, MI τ' q m) →
      SI (τ + 1) p (R.st A (τ + 1) p) ∧ ∀ x, ∀ m ∈ R.out A p τ x, MI τ p m) :
    ∀ τ, (∀ p, SI τ p (R.st A τ p)) ∧ ∀ τ' < τ, ∀ q x m, m ∈ R.out A q τ' x → MI τ' q m := by
  intro τ
  induction τ with
  | zero => exact ⟨h0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ τ ih =>
    obtain ⟨ihS, ihM⟩ := ih
    have hin : ∀ p q m, (q, m) ∈ R.inbox A p τ → ∃ τ' < τ, MI τ' q m := by
      intro p q m h
      obtain ⟨τ', hτ', -, hm⟩ := (mem_inbox A R hR).1 h
      exact ⟨τ', hτ', ihM τ' hτ' q p m hm⟩
    refine ⟨fun p => ?_, fun τ' hτ' q x m hm => ?_⟩
    · by_cases ha : R.alive p τ
      · exact (hstep τ p ha (ihS p) (hin p)).1
      · rw [st_succ_of_not_alive A R (by simpa using ha)]
        exact hmono _ _ _ (ihS p)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hτ' with h | rfl
      · exact ihM τ' h q x m hm
      · by_cases ha : R.alive q τ'
        · exact (hstep τ' q ha (ihS q) (hin q)).2 x m hm
        · rw [out_of_not_alive A R (by simpa using ha)] at hm
          simp at hm

/-- The state invariant of `Run.invariant`. -/
theorem invariant_st (hR : IsOrder R.ord) (SI : ℕ → P → S → Prop) (MI : ℕ → P → M → Prop)
    (h0 : ∀ p, SI 0 p (A.init p))
    (hmono : ∀ τ p s, SI τ p s → SI (τ + 1) p s)
    (hstep : ∀ τ p, R.alive p τ → SI τ p (R.st A τ p) →
      (∀ q m, (q, m) ∈ R.inbox A p τ → ∃ τ' < τ, MI τ' q m) →
      SI (τ + 1) p (R.st A (τ + 1) p) ∧ ∀ x, ∀ m ∈ R.out A p τ x, MI τ p m)
    (τ : ℕ) (p : P) : SI τ p (R.st A τ p) :=
  (invariant A R hR SI MI h0 hmono hstep τ).1 p

/-- The message invariant of `Run.invariant`. -/
theorem invariant_out (hR : IsOrder R.ord) (SI : ℕ → P → S → Prop) (MI : ℕ → P → M → Prop)
    (h0 : ∀ p, SI 0 p (A.init p))
    (hmono : ∀ τ p s, SI τ p s → SI (τ + 1) p s)
    (hstep : ∀ τ p, R.alive p τ → SI τ p (R.st A τ p) →
      (∀ q m, (q, m) ∈ R.inbox A p τ → ∃ τ' < τ, MI τ' q m) →
      SI (τ + 1) p (R.st A (τ + 1) p) ∧ ∀ x, ∀ m ∈ R.out A p τ x, MI τ p m)
    {τ : ℕ} {q x : P} {m : M} (hm : m ∈ R.out A q τ x) : MI τ q m :=
  (invariant A R hR SI MI h0 hmono hstep (τ + 1)).2 τ (by omega) q x m hm

/-- Messages in an inbox satisfy the message invariant at some earlier time. -/
theorem invariant_inbox (hR : IsOrder R.ord) (SI : ℕ → P → S → Prop) (MI : ℕ → P → M → Prop)
    (h0 : ∀ p, SI 0 p (A.init p))
    (hmono : ∀ τ p s, SI τ p s → SI (τ + 1) p s)
    (hstep : ∀ τ p, R.alive p τ → SI τ p (R.st A τ p) →
      (∀ q m, (q, m) ∈ R.inbox A p τ → ∃ τ' < τ, MI τ' q m) →
      SI (τ + 1) p (R.st A (τ + 1) p) ∧ ∀ x, ∀ m ∈ R.out A p τ x, MI τ p m)
    {τ : ℕ} {q x : P} {m : M} (hm : (q, m) ∈ R.inbox A x τ) : ∃ τ' < τ, MI τ' q m := by
  obtain ⟨τ', hτ', -, h⟩ := (mem_inbox A R hR).1 hm
  exact ⟨τ', hτ', invariant_out A R hR SI MI h0 hmono hstep h⟩

/-- A property of local states preserved by every step of `p` persists. -/
theorem st_mono (Φ : S → Prop) {p : P}
    (h : ∀ τ s inv l, Φ s → Φ (A.step p τ s inv l)) {τ τ' : ℕ} (hle : τ ≤ τ')
    (hΦ : Φ (R.st A τ p)) : Φ (R.st A τ' p) := by
  induction hle with
  | refl => exact hΦ
  | step _ ih =>
    rw [st_succ]
    split_ifs
    · exact h _ _ _ _ ih
    · exact ih

end Run

variable {P V M S : Type*} [DecidableEq P]

/-! ### Synchronous runs -/

/-- The `E`-faulty synchronous run (Definition 2 of [RyabininGotsmanSutra2025]): the processes of
`E` crash at the beginning of the first round, all others are correct, every message sent in a round
is delivered at the beginning of the next one. The invocations and the delivery order are
parameters. -/
def syncRun (E : Finset P) (inv : P → ℕ → Option V) (ord : P → ℕ → List (P × M) → List (P × M)) :
    Run P V M where
  crash p := if p ∈ E then some 0 else none
  gst := 0
  inv := inv
  dl _ τ _ := τ + 1
  ord := ord

theorem syncRun_crash_of_mem {E : Finset P} {inv : P → ℕ → Option V}
    {ord : P → ℕ → List (P × M) → List (P × M)} {p : P} (h : p ∈ E) :
    (syncRun E inv ord).crash p = some 0 := by simp [syncRun, h]

theorem syncRun_crash_of_not_mem {E : Finset P} {inv : P → ℕ → Option V}
    {ord : P → ℕ → List (P × M) → List (P × M)} {p : P} (h : p ∉ E) :
    (syncRun E inv ord).crash p = none := by simp [syncRun, h]

theorem syncRun_faulty [Fintype P] (E : Finset P) (inv : P → ℕ → Option V)
    (ord : P → ℕ → List (P × M) → List (P × M)) : (syncRun E inv ord).faulty = E := by
  ext p; by_cases h : p ∈ E <;> simp [Run.faulty, syncRun, h]

theorem syncRun_valid [Fintype P] {f : ℕ} {E : Finset P} (hE : E.card ≤ f) (inv : P → ℕ → Option V)
    {ord : P → ℕ → List (P × M) → List (P × M)} (ho : IsOrder ord) :
    (syncRun E inv ord).Valid f where
  card_faulty := by rw [syncRun_faulty]; exact hE
  ord_perm := ho
  dl_ge _ _ _ _ _ := le_rfl
  dl_le _ τ _ _ _ := by simp [syncRun]

end Cslib.CrashPartialSync
