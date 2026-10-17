/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.BinaryConsensus
public import Mathlib.Data.Set.Card

/-!
# Vector consensus at optimal resilience `n > 3t`: the protocol

A deterministic, unauthenticated, partially synchronous Byzantine **vector consensus** protocol,
written as a round algorithm (`Cslib.Byzantine.PartialSync.Rounds`). Correct processes decide a
common vector of exactly `n - t` process-proposal pairs in which every pair `(q, x)` with `q`
correct is `q`'s actual proposal (*vector validity*), for any `n > 3t`.

The design is PBFT-like [CastroLiskov1999], with views of 5 rounds and leader `leader u` for
view `u`:

0. **status**: every process broadcasts its status `σ = (input, prepared, acc)`: its proposal,
   its last *prepared* pair `(view, vector)`, and the list of all `(view, vector)` it accepted;
1. **echo**: every process re-broadcasts the statuses it received in round 0;
2. **propose**: the leader broadcasts `(m, S)`, where `S` is a set of statuses (those it
   received directly and saw echoed `2t + 1` times) and `m` is *justified* by `S`; a process
   accepts `(m, S)` iff every status in `S` is *confirmed* for it (received directly or echoed
   `t + 1` times) and `m` is justified by `S`:
   * *fresh*: `n - t` statuses of `S` have prepared nothing, and `m` consists of `n - t` inputs
     read from `S`; or
   * *locked*: for some view `v`, `n - t` statuses of `S` prepared nothing, or prepared at a view
     `< v`, or prepared `(v, m)`; and `t + 1` statuses of `S` accepted `m` at a view `≥ v`;
3. **prepare**: a process that accepted `m` broadcasts `prepare m`; on `n - t` of them it
   prepares `(u, m)`;
4. **commit**: a process that prepared `(u, m)` in this view broadcasts `commit m`; on
   `n - t` of them it decides `m`.

Echoing makes the leader's evidence `S` checkable without signatures (cf. the view-change
acknowledgements of PBFT's MAC variant); the "locked" rule is PBFT's new-view rule.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync.VC

open Finset

variable {P VI : Type*} [Fintype P] [DecidableEq P]

/-- Vectors: partial assignments of proposals to processes. -/
abbrev Vec (P VI : Type*) := Config P VI

/-- A status report. -/
structure Status (P VI : Type*) where
  /-- The proposal of the reporting process. -/
  input : VI
  /-- The last prepared `(view, vector)`, if any. -/
  prepared : Option (ℕ × Vec P VI)
  /-- All accepted `(view, vector)` pairs. -/
  acc : List (ℕ × Vec P VI)

/-- Protocol messages. -/
inductive Msg (P VI : Type*)
  | status (σ : Status P VI)
  | echo (e : P → Option (Status P VI))
  | propose (m : Vec P VI) (S : P → Option (Status P VI))
  | prepare (m : Vec P VI)
  | commit (m : Vec P VI)

/-- Local state. -/
structure LState (P VI : Type*) where
  /-- The own proposal. -/
  input : VI
  /-- The last prepared `(view, vector)`, if any. -/
  prepared : Option (ℕ × Vec P VI)
  /-- All accepted `(view, vector)` pairs. -/
  acc : List (ℕ × Vec P VI)
  /-- The decision, if any. -/
  dec : Option (Vec P VI)
  /-- statuses received in the status round of the current view -/
  st0 : P → Option (Status P VI)
  /-- echoes received in the echo round of the current view -/
  ech : P → Option (P → Option (Status P VI))
  /-- the vector accepted in the current view -/
  cur : Option (Vec P VI)

namespace Msg

/-- The status carried by a message, if any. -/
def getStatus : Option (Msg P VI) → Option (Status P VI)
  | some (status σ) => some σ
  | _ => none

/-- The echo carried by a message, if any. -/
def getEcho : Option (Msg P VI) → Option (P → Option (Status P VI))
  | some (echo e) => some e
  | _ => none

/-- The proposal carried by a message, if any. -/
def getPropose : Option (Msg P VI) → Option (Vec P VI × (P → Option (Status P VI)))
  | some (propose m S) => some (m, S)
  | _ => none

end Msg

/-- Number of processes satisfying a predicate. -/
noncomputable def cnt (f : P → Prop) : ℕ := Set.ncard {q | f q}

/-- The status a process broadcasts. -/
def LState.status (s : LState P VI) : Status P VI := ⟨s.input, s.prepared, s.acc⟩

variable (t : ℕ)

/-- Number of echoes (received by `s`) reporting that `j`'s status is `σ`. -/
noncomputable def echoCount (s : LState P VI) (j : P) (σ : Status P VI) : ℕ :=
  cnt fun k => ∃ e, s.ech k = some e ∧ e j = some σ

/-- Every status of `S` is confirmed: received directly, or echoed `t + 1` times. -/
def Confirmed (s : LState P VI) (S : P → Option (Status P VI)) : Prop :=
  ∀ j σ, S j = some σ → s.st0 j = some σ ∨ t + 1 ≤ echoCount s j σ

/-- *Fresh* justification: `n - t` statuses prepared nothing; `m` consists of `n - t` inputs
read from `S`. -/
def Fresh (S : P → Option (Status P VI)) (m : Vec P VI) : Prop :=
  Fintype.card P - t ≤ cnt (fun j => ∃ σ, S j = some σ ∧ σ.prepared = none) ∧
  m.procs.card = Fintype.card P - t ∧ ∀ q x, m q = some x → ∃ σ, S q = some σ ∧ σ.input = x

/-- *Locked* justification (PBFT's new-view rule). -/
def Locked (S : P → Option (Status P VI)) (m : Vec P VI) : Prop :=
  ∃ v, Fintype.card P - t ≤ cnt (fun j => ∃ σ, S j = some σ ∧
      ∀ v' m', σ.prepared = some (v', m') → v' < v ∨ (v' = v ∧ m' = m)) ∧
    t + 1 ≤ cnt (fun j => ∃ σ, S j = some σ ∧ ∃ v'', v ≤ v'' ∧ (v'', m) ∈ σ.acc)

/-- `m` is justified by `S`. -/
def Justified (S : P → Option (Status P VI)) (m : Vec P VI) : Prop := Fresh t S m ∨ Locked t S m

/-- Acceptance test of a proposal `(m, S)`. -/
def Accept (s : LState P VI) (S : P → Option (Status P VI)) (m : Vec P VI) : Prop :=
  Confirmed t s S ∧ Justified t S m

/-- The leader's evidence: statuses received directly and echoed `2t + 1` times. -/
noncomputable def leaderS (s : LState P VI) : P → Option (Status P VI) := by
  classical exact fun j =>
    if h : ∃ σ, s.st0 j = some σ ∧ 2 * t + 1 ≤ echoCount s j σ then some h.choose else none

/-- The leader's proposal: some vector justified by its evidence. -/
noncomputable def leaderM (s : LState P VI) : Vec P VI := by
  classical exact
    if h : ∃ m, Justified t (leaderS t s) m then h.choose else fun _ => none

variable (leader : ℕ → P)

/-- The protocol as a round algorithm (round `r` is step `r % 5` of view `r / 5`). -/
noncomputable def algo : RoundAlgorithm P (Msg P VI) (LState P VI) VI (Vec P VI) where
  init _ v := ⟨v, none, [], none, fun _ => none, fun _ => none, none⟩
  send r p s _ :=
    if r % 5 = 0 then some (.status s.status)
    else if r % 5 = 1 then some (.echo s.st0)
    else if r % 5 = 2 then
      (if p = leader (r / 5) then some (.propose (leaderM t s) (leaderS t s)) else none)
    else if r % 5 = 3 then s.cur.map .prepare
    else s.prepared.bind fun vm => if vm.1 = r / 5 then some (.commit vm.2) else none
  trans r _ s rcv := by
    classical exact
    if r % 5 = 0 then { s with st0 := fun j => Msg.getStatus (rcv j) }
    else if r % 5 = 1 then { s with ech := fun k => Msg.getEcho (rcv k) }
    else if r % 5 = 2 then
      (if h : ∃ m S, Msg.getPropose (rcv (leader (r / 5))) = some (m, S) ∧ Accept t s S m then
        { s with cur := some h.choose, acc := (r / 5, h.choose) :: s.acc }
      else { s with cur := none })
    else if r % 5 = 3 then
      (if h : ∃ m, Fintype.card P - t ≤ cnt (fun q => rcv q = some (.prepare m)) then
        { s with prepared := some (r / 5, h.choose) }
      else s)
    else
      (if h : s.dec = none ∧ ∃ m, Fintype.card P - t ≤ cnt (fun q => rcv q = some (.commit m)) then
        { s with dec := some h.2.choose }
      else s)
  decide _ s := s.dec

end Cslib.Byzantine.PartialSync.VC
