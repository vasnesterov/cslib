/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.SelfStabilization.Defs
public import Cslib.Computability.Distributed.SelfStabilization.StoneAge
public import Mathlib.Combinatorics.Digraph.Basic

/-!
# Daemons: activation schedules, executions and rounds

Deterministic algorithms in the *atomic-state* (locally shared memory) style: a configuration is
`γ : V → Q`, and `next γ p` is the state that process `p` takes if it is activated in `γ` (each
process has a single deterministic action; several guarded actions with pairwise exclusive guards
are folded into one `next`). A *daemon* (scheduler) chooses, at every step `t`, the set `S t` of
activated processes; activated processes move, the others keep their state (`stepSet`; a
stone-age step is the instance `next C v = δ (C v) (signal G C v)`,
`Cslib.StoneAge.step_eq_stepSet`). The usual daemons are classes of executions:

* the **distributed unfair daemon**: `IsUnfairRun next e S` — only enabled processes are activated,
  some process is activated at every non-terminal configuration, and a terminal configuration
  repeats forever (executions in `Ext∞` form, so finite executions are the eventually terminal
  ones); `IsUnfairExec next`;
* the **synchronous daemon**: `IsSyncExec next e`, i.e. `e (t+1) = next (e t)` (all processes are
  activated; equivalently all enabled processes, `IsSyncExec.isUnfairRun`).

Fairness of a schedule `S : ℕ → Set V`: weak fairness is `Cslib.StoneAge.Fair` (every process is
activated infinitely often), with the round operator `Cslib.StoneAge.rho`; `BoundedFair r S`
(every process is activated in every window of `r` steps) implies it (`BoundedFair.fair`) and
bounds the length of rounds (`BoundedFair.rho_le`).

Rounds of the unfair daemon are defined through enabledness: `RoundDone e S s s'` (every process
enabled at `s` executes an action or is neutralized during `[s, s']`), `RoundBounds e S r`
(each `[r i, r (i+1)]` contains a complete round) and `IsLeastRoundBounds e S r` (the least
such bounds).

`SilentSelfStabilizing next Exec P`: every execution of the class reaches a terminal
configuration, and terminal configurations satisfy `P`; then the terminal configurations are
legitimate (`SilentSelfStabilizing.isLegitimate`).

`IsLocal G next`: on a digraph, the next state of `p` only depends on the inputs and states of `p`
and its predecessors; `syncExec_agree`: synchronous executions agree forever on a
predecessor-closed set on which they agree initially.
-/

@[expose] public section

namespace Cslib.SelfStabilization

variable {V Q : Type*}

section Exec

variable (next : (V → Q) → V → Q)

/-- `p` is enabled in `γ`: its action would change its state. -/
def Enabled (γ : V → Q) (p : V) : Prop := next γ p ≠ γ p

/-- `γ` is terminal: no process is enabled. -/
def Terminal (γ : V → Q) : Prop := ∀ p, next γ p = γ p

open Classical in
/-- One step in which the processes of `S` are activated: they take their next state, the
others keep their state. -/
noncomputable def stepSet (S : Set V) (γ : V → Q) : V → Q :=
  fun p => if p ∈ S then next γ p else γ p

/-- An execution under the distributed unfair daemon, with activated sets `S t` (`Ext∞` form):
only enabled processes are activated, activated processes move, the others keep their state, and
some process is activated unless the configuration is terminal. -/
structure IsUnfairRun (e : ℕ → V → Q) (S : ℕ → Set V) : Prop where
  /-- Only enabled processes are activated. -/
  enabled : ∀ t p, p ∈ S t → Enabled next (e t) p
  /-- Activated processes take their next state. -/
  move : ∀ t p, p ∈ S t → e (t + 1) p = next (e t) p
  /-- The other processes keep their state. -/
  stay : ∀ t p, p ∉ S t → e (t + 1) p = e t p
  /-- Some process is activated unless the configuration is terminal. -/
  progress : ∀ t, (S t).Nonempty ∨ Terminal next (e t)

/-- An execution under the distributed unfair daemon. -/
def IsUnfairExec (e : ℕ → V → Q) : Prop := ∃ S, IsUnfairRun next e S

/-- An execution under the synchronous daemon. -/
def IsSyncExec (e : ℕ → V → Q) : Prop := ∀ t, e (t + 1) = next (e t)

/-- Every process enabled at `s` executes an action or is neutralized during `[s, s']`. -/
def RoundDone (e : ℕ → V → Q) (S : ℕ → Set V) (s s' : ℕ) : Prop :=
  ∀ p, Enabled next (e s) p → ∃ u, s ≤ u ∧ u < s' ∧ (p ∈ S u ∨ ¬ Enabled next (e (u + 1)) p)

/-- `r` is a sequence of times starting at `0` such that each `[r i, r (i+1)]` contains a complete
round. In particular `r` dominates the least round boundaries (see `IsLeastRoundBounds`). -/
def RoundBounds (e : ℕ → V → Q) (S : ℕ → Set V) (r : ℕ → ℕ) : Prop :=
  r 0 = 0 ∧ ∀ i, r i ≤ r (i + 1) ∧ RoundDone next e S (r i) (r (i + 1))

/-- The rounds of an execution: `r (i+1)` is the end of the minimal prefix of the suffix starting
at `r i` in which every process enabled at `r i` executes or is neutralized. -/
def IsLeastRoundBounds (e : ℕ → V → Q) (S : ℕ → Set V) (r : ℕ → ℕ) : Prop :=
  RoundBounds next e S r ∧
    ∀ i s', r i ≤ s' → RoundDone next e S (r i) s' → r (i + 1) ≤ s'

/-- *Silent* self-stabilization for a class of executions and a predicate `P` on configurations:
every execution reaches a terminal configuration and every terminal configuration satisfies `P`. -/
def SilentSelfStabilizing (Exec : Set (ℕ → V → Q)) (P : (V → Q) → Prop) : Prop :=
  (∀ e ∈ Exec, ∃ t, Terminal next (e t)) ∧ ∀ γ, Terminal next γ → P γ

variable {next}

/-- Activated processes take their next state. -/
@[simp]
theorem stepSet_of_mem {S : Set V} {γ : V → Q} {p : V} (hp : p ∈ S) :
    stepSet next S γ p = next γ p := by
  classical
  simp [stepSet, hp]

/-- Processes that are not activated keep their state. -/
@[simp]
theorem stepSet_of_not_mem {S : Set V} {γ : V → Q} {p : V} (hp : p ∉ S) :
    stepSet next S γ p = γ p := by
  classical
  simp [stepSet, hp]

/-- Activating every process is a synchronous step. -/
@[simp]
theorem stepSet_univ (γ : V → Q) : stepSet next Set.univ γ = next γ :=
  funext fun _ => stepSet_of_mem (Set.mem_univ _)

/-- No process is activated at a terminal configuration. -/
theorem IsUnfairRun.not_mem_of_terminal {e : ℕ → V → Q} {S : ℕ → Set V}
    (h : IsUnfairRun next e S) {t : ℕ} (ht : Terminal next (e t)) (p : V) : p ∉ S t :=
  fun hp => h.enabled t p hp (ht p)

/-- A terminal configuration is followed by itself. -/
theorem IsUnfairRun.succ_eq_of_terminal {e : ℕ → V → Q} {S : ℕ → Set V}
    (h : IsUnfairRun next e S) {t : ℕ} (ht : Terminal next (e t)) : e (t + 1) = e t :=
  funext fun p => h.stay t p (h.not_mem_of_terminal ht p)

/-- A terminal configuration repeats forever. -/
theorem IsUnfairRun.eq_of_terminal {e : ℕ → V → Q} {S : ℕ → Set V} (h : IsUnfairRun next e S)
    {t : ℕ} (ht : Terminal next (e t)) : ∀ u, t ≤ u → e u = e t := by
  intro u hu
  induction hu with
  | refl => rfl
  | step _ ih => rw [h.succ_eq_of_terminal (ih ▸ ht), ih]

/-- The suffix of a run is a run. -/
theorem IsUnfairRun.shift {e : ℕ → V → Q} {S : ℕ → Set V} (h : IsUnfairRun next e S) (k : ℕ) :
    IsUnfairRun next (fun t => e (k + t)) (fun t => S (k + t)) where
  enabled t p hp := h.enabled (k + t) p hp
  move t p hp := h.move (k + t) p hp
  stay t p hp := h.stay (k + t) p hp
  progress t := h.progress (k + t)

/-- If a run is eventually constant, it reaches a terminal configuration. -/
theorem IsUnfairRun.terminal_of_const {e : ℕ → V → Q} {S : ℕ → Set V} (h : IsUnfairRun next e S)
    {T : ℕ} (hT : ∀ t, T ≤ t → e t = e T) : Terminal next (e T) := by
  rcases h.progress T with ⟨p, hp⟩ | ht
  · exact absurd (by rw [← h.move T p hp, hT (T + 1) (by omega)]) (h.enabled T p hp)
  · exact ht

/-- The activated sets of a synchronous execution: the enabled processes. -/
def syncSet (e : ℕ → V → Q) (t : ℕ) : Set V := {p | Enabled next (e t) p}

/-- A synchronous execution is a run of the distributed unfair daemon, activating exactly the
enabled processes. -/
theorem IsSyncExec.isUnfairRun {e : ℕ → V → Q} (h : IsSyncExec next e) :
    IsUnfairRun next e (syncSet (next := next) e) where
  enabled _ _ hp := hp
  move t p _ := by rw [h t]
  stay t p hp := by
    rw [h t]; simpa [syncSet, Enabled] using hp
  progress t := by
    by_cases ht : Terminal next (e t)
    · exact Or.inr ht
    · simp only [Terminal, not_forall] at ht
      exact Or.inl ht

/-- The synchronous daemon is a special case of the distributed unfair daemon. -/
theorem IsSyncExec.isUnfairExec {e : ℕ → V → Q} (h : IsSyncExec next e) :
    IsUnfairExec next e :=
  ⟨_, h.isUnfairRun⟩

/-- The suffix of a synchronous execution is a synchronous execution. -/
theorem IsSyncExec.shift {e : ℕ → V → Q} (h : IsSyncExec next e) (k : ℕ) :
    IsSyncExec next (fun t => e (k + t)) := fun t => h (k + t)

/-- Iterating `next` gives the synchronous execution from `γ`. -/
theorem isSyncExec_iterate (γ : V → Q) : IsSyncExec next (fun t => next^[t] γ) := fun t => by
  simp only [Function.iterate_succ_apply']

/-- A synchronous execution is the iteration of `next` from its initial configuration. -/
theorem IsSyncExec.eq_iterate {e : ℕ → V → Q} (h : IsSyncExec next e) (t : ℕ) :
    e t = next^[t] (e 0) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [h t, ih, Function.iterate_succ_apply']

/-- Under the synchronous daemon, every step is a round. -/
theorem IsSyncExec.roundBounds {e : ℕ → V → Q} (_h : IsSyncExec next e) :
    RoundBounds next e (syncSet (next := next) e) id :=
  ⟨rfl, fun i => ⟨Nat.le_succ i, fun _ hp => ⟨i, le_rfl, Nat.lt_succ_self i, Or.inl hp⟩⟩⟩

/-- A complete round within `[s, s']` is a complete round within any larger window. -/
theorem RoundDone.mono_right {e : ℕ → V → Q} {S : ℕ → Set V} {s s' s'' : ℕ}
    (h : RoundDone next e S s s') (hs : s' ≤ s'') : RoundDone next e S s s'' := fun p hp =>
  let ⟨u, h1, h2, h3⟩ := h p hp; ⟨u, h1, by omega, h3⟩

/-- Round bounds are monotone. -/
theorem RoundBounds.mono {e : ℕ → V → Q} {S : ℕ → Set V} {r : ℕ → ℕ}
    (h : RoundBounds next e S r) : Monotone r :=
  monotone_nat_of_le_succ fun i => (h.2 i).1

/-- The least round boundaries are round bounds. -/
theorem IsLeastRoundBounds.roundBounds {e : ℕ → V → Q} {S : ℕ → Set V} {r : ℕ → ℕ}
    (h : IsLeastRoundBounds next e S r) : RoundBounds next e S r := h.1

/-- In an eventually terminal run, the least round boundaries exist. -/
theorem IsUnfairRun.exists_isLeastRoundBounds {e : ℕ → V → Q} {S : ℕ → Set V}
    (h : IsUnfairRun next e S) {T : ℕ} (hT : Terminal next (e T)) :
    ∃ r, IsLeastRoundBounds next e S r := by
  classical
  have hex : ∀ s, ∃ s', s ≤ s' ∧ RoundDone next e S s s' := by
    intro s
    refine ⟨max s T + 1, by omega, fun p _ => ⟨max s T, le_max_left _ _, by omega, Or.inr ?_⟩⟩
    have := h.eq_of_terminal hT (max s T + 1) (by omega)
    rw [this]; exact fun hp => hp (hT p)
  let f : ℕ → ℕ := fun s => Nat.find (hex s)
  let r : ℕ → ℕ := fun i => f^[i] 0
  refine ⟨r, ⟨rfl, fun i => ?_⟩, fun i s' hs' hd => ?_⟩
  · have := Nat.find_spec (hex (r i))
    simp only [r, Function.iterate_succ_apply']
    exact this
  · simp only [r, Function.iterate_succ_apply']
    exact Nat.find_min' (hex _) ⟨hs', hd⟩

/-- Under silent self-stabilization, the terminal configurations are legitimate for every
specification that holds on all executions starting in a terminal configuration satisfying `P`. -/
theorem SilentSelfStabilizing.isLegitimate {Exec : Set (ℕ → V → Q)} {P : (V → Q) → Prop}
    {SP : (ℕ → V → Q) → Prop} (h : SilentSelfStabilizing next Exec P)
    (hSP : ∀ e ∈ Exec, Terminal next (e 0) → P (e 0) → SP e) :
    IsLegitimate Exec SP {γ | Terminal next γ} :=
  ⟨h.1, fun e he h0 => hSP e he h0 (h.2 _ h0)⟩

/-- Silent self-stabilization implies self-stabilization (see `isLegitimate`). -/
theorem SilentSelfStabilizing.selfStabilizing {Exec : Set (ℕ → V → Q)} {P : (V → Q) → Prop}
    {SP : (ℕ → V → Q) → Prop} (h : SilentSelfStabilizing next Exec P)
    (hSP : ∀ e ∈ Exec, Terminal next (e 0) → P (e 0) → SP e) : SelfStabilizing Exec SP :=
  ⟨_, h.isLegitimate hSP⟩

/-- Silent self-stabilization is inherited by subclasses of executions. -/
theorem SilentSelfStabilizing.mono {Exec Exec' : Set (ℕ → V → Q)} {P : (V → Q) → Prop}
    (h : SilentSelfStabilizing next Exec P) (hE : Exec' ⊆ Exec) :
    SilentSelfStabilizing next Exec' P :=
  ⟨fun e he => h.1 e (hE he), h.2⟩

end Exec

/-! ### Fairness of schedules -/

section Fairness

open Cslib.StoneAge

/-- *Bounded fairness*: every process is activated at least once in every window of `r`
consecutive steps. -/
def BoundedFair (r : ℕ) (S : ℕ → Set V) : Prop := ∀ t v, ∃ s, t ≤ s ∧ s < t + r ∧ v ∈ S s

variable {r r' : ℕ} {S : ℕ → Set V}

/-- Bounded fairness with window `r` implies bounded fairness with any larger window. -/
theorem BoundedFair.mono (h : BoundedFair r S) (hr : r ≤ r') : BoundedFair r' S := fun t v =>
  let ⟨s, h1, h2, h3⟩ := h t v; ⟨s, h1, by omega, h3⟩

/-- Bounded fairness implies (weak) fairness. -/
theorem BoundedFair.fair (h : BoundedFair r S) : Fair S := fun v t =>
  let ⟨s, h1, _, h3⟩ := h t v; ⟨s, h1, h3⟩

/-- Bounded fairness is the coverage of every window `[t, t + r)` in the sense of the stone-age
round operator (`Cslib.StoneAge.Covered`). -/
theorem boundedFair_iff_covered : BoundedFair r S ↔ ∀ t, Covered S t (t + r) := Iff.rfl

/-- Under bounded fairness, a round (`Cslib.StoneAge.rho`) lasts at most `r` steps. -/
theorem BoundedFair.rho_le (h : BoundedFair r S) (t : ℕ) : rho S t ≤ t + r :=
  rho_le_of_covered (h t) (Nat.le_add_right t r)

end Fairness

/-! ### Locality on digraphs -/

section Local

variable {I : Type*}

/-- Locality of an algorithm on the digraph `G`, parameterised by the input assignment `ι`
(e.g. identifiers): the next state of `p` only depends on the inputs and states of `p` and of its
predecessors. -/
def IsLocal (G : Digraph V) (next : (V → I) → (V → Q) → V → Q) : Prop :=
  ∀ ι ι' γ γ' p, (∀ q, (q = p ∨ G.Adj q p) → ι q = ι' q ∧ γ q = γ' q) →
    next ι γ p = next ι' γ' p

/-- Two synchronous executions whose inputs and initial configurations agree on a
predecessor-closed set `S` agree on `S` forever. -/
theorem syncExec_agree {G : Digraph V} {next : (V → I) → (V → Q) → V → Q} (hloc : IsLocal G next)
    {S : Set V} (hS : ∀ p ∈ S, ∀ q, G.Adj q p → q ∈ S) {ι ι' : V → I} (hι : ∀ p ∈ S, ι p = ι' p)
    {e e' : ℕ → V → Q} (he : IsSyncExec (next ι) e) (he' : IsSyncExec (next ι') e')
    (h0 : ∀ p ∈ S, e 0 p = e' 0 p) : ∀ t, ∀ p ∈ S, e t p = e' t p := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    intro p hp
    rw [he t, he' t]
    apply hloc
    rintro q (rfl | hq)
    · exact ⟨hι _ hp, ih _ hp⟩
    · exact ⟨hι _ (hS p hp q hq), ih _ (hS p hp q hq)⟩

end Local

end Cslib.SelfStabilization

/-! ### The stone-age model as an instance -/

namespace Cslib.StoneAge

open Cslib.SelfStabilization

variable {V Q : Type*} {G : SimpleGraph V}

/-- A stone-age step activates the set `A` for the local rule `C v ↦ δ (C v) (signal G C v)`. -/
theorem step_eq_stepSet (P : Algorithm Q) (A : Set V) (C : V → Q) :
    step G P A C = stepSet (fun C v => P.δ (C v) (signal G C v)) A C := by
  classical
  funext v
  by_cases hv : v ∈ A <;> simp [step, hv]

/-- Under the synchronous schedule, stone-age executions are synchronous executions. -/
theorem run_sync_mem_isSyncExec (P : Algorithm Q) (C0 : V → Q) :
    IsSyncExec (fun C v => P.δ (C v) (signal G C v)) (run G P C0 sync) := fun t => by
  rw [isRun_run G P C0 sync t, step_eq_stepSet, sync, stepSet_univ]

end Cslib.StoneAge
