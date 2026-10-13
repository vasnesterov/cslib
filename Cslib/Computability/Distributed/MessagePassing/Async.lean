/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.History
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Asynchronous crash-prone message passing implementing a shared object

Model `CAMP_{n,t}` ("crash asynchronous message passing"): processes `P` (finitely many in
applications) communicate over a complete network of reliable, **not necessarily FIFO**,
asynchronous channels; processes may crash.

* A `Protocol P A L M Act` describes how each process (local states `L`) reacts to
  - an invocation of an operation of the implemented object `A` (`invoke`),
  - an internal action `a : Act` (used for the continuations after `wait` statements),
  - the reception of a message `m : M` from a process `q` (`receive`).
  Each transition returns the new local state, the messages sent (a multiset of
  `(destination, message)`) and possibly a response. `none` means "not enabled": a `wait`
  condition that does not hold yet, or (for `receive`) a message that cannot be processed yet
  (it stays in the channel; this is exactly a message handler blocked at a `wait`).
  Each transition is atomic (local computation between two `wait`s is atomic).
* A configuration (`Config`) consists of the local states, the multiset of messages in transit
  (`net`, entries `(sender, receiver, message)`: channels are unordered), the multiset of all
  messages ever sent (`sent`, ghost, for message complexity) and the set of crashed processes.
* Steps (`Step`): invocation, internal action, reception, crash, `drop` (a message *whose sender
  has crashed* may be lost — this models a crash in the middle of a sequence of sends, and is a
  generalization: dropping is never forced), and `skip` (stuttering, so that infinite executions
  exist).
* `Reach C h`: `C` is reachable with history `h` (invocations and responses, as CSLib
  `Label`s, so that `Cslib.SharedMemory.IsLinearization` applies directly).
* Infinite executions (`Exec`), correct processes (never crash), weak fairness (`Exec.Fair`: a
  step of a correct process — internal action or reception — that stays enabled forever is
  eventually taken; for receptions this is channel reliability), `t`-resilience
  (`Exec.Resilient`), and the liveness property `Exec.OpsTerminate` (every operation invoked by a
  correct process returns).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace Cslib.AsyncMP

open Cslib.SharedMemory

/-- An asynchronous message-passing implementation of the object `A` by processes `P` with local
states `L`, messages `M` and internal actions `Act`. -/
structure Protocol (P : Type) (A : ObjSpec) (L M Act : Type) where
  /-- Initial local states. -/
  init : P → L
  /-- `invoke p o l`: process `p` in state `l` invokes `o`. -/
  invoke : P → A.Op → L → Option (L × Multiset (P × M))
  /-- `internal p a l`: internal action `a` of `p` (e.g. the end of a `wait`). -/
  internal : P → Act → L → Option (L × Multiset (P × M) × Option A.Resp)
  /-- `receive p q m l`: process `p` processes message `m` received from `q`. -/
  receive : P → P → M → L → Option (L × Multiset (P × M) × Option A.Resp)

/-- Global configurations. -/
structure Config (P L M : Type) where
  /-- Local states. -/
  loc : P → L
  /-- Messages in transit `(sender, receiver, message)` (unordered channels). -/
  net : Multiset (P × P × M)
  /-- All messages sent so far (ghost; for message complexity). -/
  sent : Multiset (P × P × M)
  /-- Crashed processes. -/
  crashed : Finset P

/-- Steps of an execution. -/
inductive Step (P : Type) (A : ObjSpec) (M Act : Type) where
  /-- Invocation of `o` by `p`. -/
  | inv (p : P) (o : A.Op)
  /-- Internal action `a` of `p`. -/
  | internal (p : P) (a : Act)
  /-- `dst` receives and processes `m` from `src`. -/
  | recv (src dst : P) (m : M)
  /-- Loss of a message whose sender has crashed. -/
  | drop (src dst : P) (m : M)
  /-- Crash of `p`. -/
  | crash (p : P)
  /-- Stuttering step. -/
  | skip

namespace Step

variable {P : Type} {A : ObjSpec} {M Act : Type}

/-- The correct process responsible for taking a step (fairness applies to these steps). -/
def owner : Step P A M Act → Option P
  | internal p _ => some p
  | recv _ dst _ => some dst
  | _ => none

end Step

/-- Tag messages with their sender. -/
def outMsgs {P M : Type} (p : P) (out : Multiset (P × M)) : Multiset (P × P × M) :=
  out.map (fun x => (p, x.1, x.2))

/-- Apply a local transition of `p` (new local state `l`, messages `out`), with `net` the network
before the new messages are added. -/
def Config.apply {P L M : Type} [DecidableEq P] (C : Config P L M) (p : P) (l : L)
    (out : Multiset (P × M)) (net : Multiset (P × P × M)) : Config P L M :=
  ⟨Function.update C.loc p l, net + outMsgs p out, C.sent + outMsgs p out, C.crashed⟩

namespace Protocol

variable {P : Type} {A : ObjSpec} {L M Act : Type} [DecidableEq P] [DecidableEq M]
variable (Pr : Protocol P A L M Act)

/-- The initial configuration. -/
def initCfg : Config P L M := ⟨Pr.init, 0, 0, ∅⟩

/-- One step; returns the new configuration and the history label (invocation/response). -/
def step (C : Config P L M) : Step P A M Act → Option (Config P L M × Option (Label P A))
  | .inv p o =>
    if p ∈ C.crashed then none else
    (Pr.invoke p o (C.loc p)).map fun x => (C.apply p x.1 x.2 C.net, some (.inv p o))
  | .internal p a =>
    if p ∈ C.crashed then none else
    (Pr.internal p a (C.loc p)).map fun x =>
      (C.apply p x.1 x.2.1 C.net, x.2.2.map (Label.ret p))
  | .recv src dst m =>
    if dst ∈ C.crashed ∨ (src, dst, m) ∉ C.net then none else
    (Pr.receive dst src m (C.loc dst)).map fun x =>
      (C.apply dst x.1 x.2.1 (C.net.erase (src, dst, m)), x.2.2.map (Label.ret dst))
  | .drop src dst m =>
    if src ∈ C.crashed ∧ (src, dst, m) ∈ C.net then
      some (⟨C.loc, C.net.erase (src, dst, m), C.sent, C.crashed⟩, none)
    else none
  | .crash p =>
    if p ∈ C.crashed then none else some (⟨C.loc, C.net, C.sent, insert p C.crashed⟩, none)
  | .skip => some (C, none)

/-- `C` is reachable, with history `h`. -/
inductive Reach : Config P L M → List (Label P A) → Prop
  | init : Reach Pr.initCfg []
  | step {C : Config P L M} {h : List (Label P A)} {s : Step P A M Act}
      {C' : Config P L M} {ℓ : Option (Label P A)} :
      Reach C h → Pr.step C s = some (C', ℓ) → Reach C' (h ++ ℓ.toList)

/-- Safety: every history of a reachable configuration is linearizable. -/
def Linearizable : Prop := ∀ C h, Pr.Reach C h → ∃ Lin, IsLinearization h Lin

/-- The step `s` is enabled in `C`. -/
def Enabled (C : Config P L M) (s : Step P A M Act) : Prop := (Pr.step C s).isSome

/-- An infinite execution. -/
structure Exec where
  /-- Configurations. -/
  cfg : ℕ → Config P L M
  /-- Steps. -/
  stp : ℕ → Step P A M Act
  /-- Labels. -/
  lbl : ℕ → Option (Label P A)
  init : cfg 0 = Pr.initCfg
  step : ∀ t, Pr.step (cfg t) (stp t) = some (cfg (t + 1), lbl t)

variable {Pr}

namespace Exec

variable (e : Pr.Exec)

/-- The history of the first `t` steps. -/
def hist (t : ℕ) : List (Label P A) := (List.range t).filterMap e.lbl

/-- `p` never crashes. -/
def Correct (p : P) : Prop := ∀ t, p ∉ (e.cfg t).crashed

/-- Weak fairness: every step of a correct process that is enabled from some time on is
eventually taken (for receptions: reliable channels). -/
def Fair : Prop :=
  ∀ (s : Step P A M Act) (p : P), s.owner = some p → e.Correct p →
    ∀ T, (∀ t ≥ T, Pr.Enabled (e.cfg t) s) → ∃ t ≥ T, e.stp t = s

/-- At most `f` processes crash. -/
def Resilient (f : ℕ) : Prop := ∀ t, (e.cfg t).crashed.card ≤ f

/-- Liveness: every operation invoked by a correct process eventually returns. -/
def OpsTerminate : Prop :=
  ∀ p, e.Correct p → ∀ T, (respsOf (e.hist T) p).length < (opsOf (e.hist T) p).length →
    ∃ t, (respsOf (e.hist T) p).length < (respsOf (e.hist t) p).length

lemma hist_succ (t : ℕ) : e.hist (t + 1) = e.hist t ++ (e.lbl t).toList := by
  simp only [hist, List.range_succ, List.filterMap_append]
  cases h : e.lbl t <;> simp [h]

/-- Every configuration of an execution is reachable. -/
lemma reach (t : ℕ) : Pr.Reach (e.cfg t) (e.hist t) := by
  induction t with
  | zero => rw [e.init]; exact Reach.init
  | succ t ih => rw [e.hist_succ]; exact Reach.step ih (e.step t)

/-- **Progress lemma.** If a monotone quantity `f` stays at `f T` only while a step `s` of a
correct process is enabled, and taking `s` while `f = f T` increases `f`, then `f` eventually
exceeds `f T`. -/
lemma eventually_gt (hf : e.Fair) {p : P} (hp : e.Correct p) (s : Step P A M Act)
    (hs : s.owner = some p) (f : ℕ → ℕ) (hmono : Monotone f) (T : ℕ)
    (hen : ∀ t ≥ T, f t = f T → Pr.Enabled (e.cfg t) s)
    (heff : ∀ t ≥ T, e.stp t = s → f t = f T → f T < f (t + 1)) : ∃ t ≥ T, f T < f t := by
  by_contra hcon
  push Not at hcon
  have hconst : ∀ t ≥ T, f t = f T := fun t ht => le_antisymm (hcon t ht) (hmono ht)
  obtain ⟨t, ht, hst⟩ := hf s p hs hp T (fun t ht => hen t ht (hconst t ht))
  have := heff t ht hst (hconst t ht)
  have := hcon (t + 1) (by omega)
  omega

/-- Iterated progress: a quantity that can always be pushed up (from time `T₀` on) eventually
reaches any bound `c`. -/
lemma eventually_ge (f : ℕ → ℕ) (c T₀ : ℕ)
    (hstep : ∀ T ≥ T₀, f T < c → ∃ t ≥ T, f T < f t) : ∃ t ≥ T₀, c ≤ f t := by
  suffices ∀ k T, T ≥ T₀ → c - f T = k → ∃ t ≥ T, c ≤ f t by
    obtain ⟨t, ht, hc⟩ := this _ T₀ le_rfl rfl
    exact ⟨t, ht, hc⟩
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro T hT hk
    by_cases hc : c ≤ f T
    · exact ⟨T, le_refl _, hc⟩
    obtain ⟨t, ht, hlt⟩ := hstep T hT (by omega)
    obtain ⟨t', ht', hc'⟩ := ih (c - f t) (by omega) t (le_trans hT ht) rfl
    exact ⟨t', le_trans ht ht', hc'⟩

end Exec

/-- Liveness of a protocol under `f`-resilience: in every fair execution with at most `f`
crashes, every operation of a correct process terminates. -/
def Live (f : ℕ) : Prop := ∀ e : Pr.Exec, e.Fair → e.Resilient f → e.OpsTerminate

end Protocol

/-! ## Generic facts on executions (used for liveness proofs) -/

namespace Protocol

variable {P : Type} {A : ObjSpec} {L M Act : Type} [DecidableEq P] [DecidableEq M]
variable {Pr : Protocol P A L M Act}

/-- Crashed processes stay crashed. -/
lemma step_crashed_mono {C C' : Config P L M} {s : Step P A M Act} {ℓ : Option (Label P A)}
    (h : Pr.step C s = some (C', ℓ)) : C.crashed ⊆ C'.crashed := by
  cases s with
  | inv p o =>
    simp only [step] at h
    split_ifs at h
    obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at hx
    rw [← hx.1]; exact fun _ h => h
  | internal p a =>
    simp only [step] at h
    split_ifs at h
    obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at hx
    rw [← hx.1]; exact fun _ h => h
  | recv src dst m =>
    simp only [step] at h
    split_ifs at h
    obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at hx
    rw [← hx.1]; exact fun _ h => h
  | drop src dst m =>
    simp only [step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
  | crash p =>
    simp only [step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact Finset.subset_insert _ _
  | skip =>
    simp only [step, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]

namespace Exec

variable (e : Pr.Exec)

lemma crashed_mono {a b : ℕ} (hab : a ≤ b) : (e.cfg a).crashed ⊆ (e.cfg b).crashed := by
  induction b, hab using Nat.le_induction with
  | base => exact fun _ h => h
  | succ b _ ih => exact ih.trans (step_crashed_mono (e.step b))

/-- Histories of an execution grow by appending. -/
lemma hist_prefix {a b : ℕ} (hab : a ≤ b) : ∃ β, e.hist b = e.hist a ++ β := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ b _ ih =>
    obtain ⟨β, hβ⟩ := ih
    exact ⟨β ++ (e.lbl b).toList, by rw [e.hist_succ, hβ, List.append_assoc]⟩

open Classical in
/-- Faulty processes are at most `f` in an `f`-resilient execution. -/
lemma card_faulty_le [Fintype P] {f : ℕ} (hres : e.Resilient f) :
    (Finset.univ.filter (fun p => ¬ e.Correct p)).card ≤ f := by
  classical
  have hex : ∀ p, ∃ T, ¬ e.Correct p → p ∈ (e.cfg T).crashed := by
    intro p
    by_cases hp : e.Correct p
    · exact ⟨0, fun h => absurd hp h⟩
    · simp only [Correct, not_forall, not_not] at hp
      obtain ⟨T, hT⟩ := hp
      exact ⟨T, fun _ => hT⟩
  choose g hg using hex
  let B := Finset.univ.sup g
  have hsub : Finset.univ.filter (fun p => ¬ e.Correct p) ⊆ (e.cfg B).crashed := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact e.crashed_mono (Finset.le_sup (Finset.mem_univ p)) (hg p hp)
  exact (Finset.card_le_card hsub).trans (hres B)

omit [DecidableEq P] in
/-- Finitely many "eventually forever" properties hold simultaneously from some time on. -/
lemma eventually_forall [Finite P] {Q : P → ℕ → Prop} (h : ∀ p, ∃ T, ∀ b ≥ T, Q p b) :
    ∃ T, ∀ p, ∀ b ≥ T, Q p b := by
  have := Fintype.ofFinite P
  choose g hg using h
  exact ⟨Finset.univ.sup g, fun p b hb => hg p b ((Finset.le_sup (Finset.mem_univ p)).trans hb)⟩

/-- **Progress lemma for decreasing quantities.** Let `f` be non-increasing from time `T` on.
If a step `s` of a correct process is enabled from time `T₁` on as long as `f` keeps the value
`f T`, and taking `s` decreases `f`, then `f` eventually drops below `f T`. -/
lemma eventually_lt (hf : e.Fair) {p : P} (hp : e.Correct p) (s : Step P A M Act)
    (hs : s.owner = some p) (f : ℕ → ℕ) (T : ℕ)
    (hanti : ∀ a b, T ≤ a → a ≤ b → f b ≤ f a) (T₁ : ℕ)
    (hen : ∀ b ≥ T₁, (∀ c, T ≤ c → c ≤ b → f c = f T) → Pr.Enabled (e.cfg b) s)
    (heff : ∀ b ≥ T, e.stp b = s → f b = f T → f (b + 1) < f T) : ∃ b ≥ T, f b < f T := by
  by_contra hcon
  push Not at hcon
  have hconst : ∀ b ≥ T, f b = f T := fun b hb => le_antisymm (hanti T b le_rfl hb) (hcon b hb)
  obtain ⟨b, hb, hst⟩ := hf s p hs hp (max T T₁) (fun b hb =>
    hen b (le_of_max_le_right hb) (fun c hc _ => hconst c hc))
  have := heff b (le_of_max_le_left hb) hst (hconst b (le_of_max_le_left hb))
  have := hconst (b + 1) (by have := le_of_max_le_left hb; omega)
  omega

/-- A quantity that is non-increasing from time `T` on and can always be decreased while
positive eventually reaches `0`. -/
lemma eventually_zero (f : ℕ → ℕ) (T : ℕ)
    (hstep : ∀ T₀ ≥ T, 0 < f T₀ → ∃ b ≥ T₀, f b < f T₀) : ∃ b ≥ T, f b = 0 := by
  suffices ∀ k T₀, T₀ ≥ T → f T₀ = k → ∃ b ≥ T₀, f b = 0 by
    obtain ⟨b, hb, h0⟩ := this _ T le_rfl rfl
    exact ⟨b, hb, h0⟩
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro T₀ hT hk
    by_cases h0 : f T₀ = 0
    · exact ⟨T₀, le_refl _, h0⟩
    obtain ⟨b, hb, hlt⟩ := hstep T₀ hT (by omega)
    obtain ⟨b', hb', h'⟩ := ih (f b) (by omega) b (le_trans hT hb) rfl
    exact ⟨b', le_trans hb hb', h'⟩

end Exec

end Protocol

end Cslib.AsyncMP
