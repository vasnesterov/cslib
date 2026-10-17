/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Synchronous lock-step Byzantine message passing

A minimal, reusable model of deterministic protocols running in synchronous lock-step rounds over a
fixed communication graph, against a static Byzantine adversary.

* A `Protocol P I M O` gives, for every party `p : P`, a message function and a decision function.
  Both are functions of the party's *local view*: its input `I` and its history (the list of inboxes
  received so far). Since protocols are deterministic, the history is the whole local state
  ("full-information" style), which makes indistinguishability arguments definitional.
* A `Scenario` fixes the Byzantine set, the inputs, the adversary's messages (an arbitrary function
  of round, sender, receiver — for deterministic protocols this covers adaptive/rushing message
  choices), and an optional set of omitted honest messages (used for "networks with omissions").
* `hist G alg s r p` is the history of `p` after `r` rounds; `Decides G alg s p o` says that the
  first decision of `p` is `o`.

The model is unauthenticated: Byzantine parties may send anything. The authenticated (ideal
signature) variant is a *restriction* on scenarios and protocols, see
`Cslib.Byzantine.LockStep.Auth`.

## Related models in CSLib

* `Cslib.Byzantine.PartialSync` is a partially synchronous model with state machines on a
  complete network; lock-step rounds are its special case `gst = 0`, `δ = 0`. A lock-step
  protocol compiles into it (`Protocol.toAlgorithm`) and behaves there as in this model
  (`toAlgorithm_st`). The models are kept separate because they suit different proofs: this one
  supports arbitrary networks and omissions, and its history-based protocols make simulations
  (covers, relabelling, relays, parallel composition) definitional; the other one supports
  asynchrony before GST, message delays and message counting.
* `Cslib.FLP` models asynchronous crash-prone consensus; this model is synchronous and Byzantine.
-/

@[expose] public section

namespace Cslib.Byzantine.LockStep

/-- What a party receives in one round: for every potential sender, a message or nothing. -/
abbrev Inbox (P M : Type*) := P → Option M

/-- A local history: the inboxes of the rounds so far, oldest first. -/
abbrev History (P M : Type*) := List (Inbox P M)

/-- A deterministic synchronous protocol. Party `p` with input `x` and history `h` sends
`send p x h q` to `q` (if `q` is a neighbour) and has decided `decide p x h` (`none` =
undecided). -/
structure Protocol (P I M O : Type*) where
  /-- The message `p` sends to `q` in the next round. -/
  send : P → I → History P M → P → Option M
  /-- The decision of `p` after having seen the history (`none` if not decided yet). -/
  decide : P → I → History P M → Option O

/-- A run's parameters: static Byzantine set, inputs, adversary messages, honest-message
omissions. -/
structure Scenario (P I M : Type*) where
  /-- The (static) set of Byzantine parties. -/
  byz : Set P
  /-- The inputs (the inputs of Byzantine parties are irrelevant). -/
  input : P → I
  /-- `adv r p q`: the message Byzantine `p` sends to `q` in round `r`. -/
  adv : ℕ → P → P → Option M
  /-- `drop r p q`: the honest message from `p` to `q` in round `r` is omitted. -/
  drop : ℕ → P → P → Prop := fun _ _ _ => False

namespace Scenario

variable {P I M : Type*}

/-- A scenario without omissions. -/
def Reliable (s : Scenario P I M) : Prop := ∀ r p q, ¬ s.drop r p q

/-- The honest parties. -/
def honest (s : Scenario P I M) : Set P := s.byzᶜ

end Scenario

variable {P I M O : Type*} (G : SimpleGraph P) (alg : Protocol P I M O)

open Classical in
/-- The message actually delivered to `q` from `p` in round `r`, given everybody's history at the
start of the round. -/
noncomputable def deliver (s : Scenario P I M) (h : P → History P M) (r : ℕ) (p q : P) : Option M :=
  if G.Adj p q then
    (if p ∈ s.byz then s.adv r p q
     else if s.drop r p q then none else alg.send p (s.input p) (h p) q)
  else none

/-- `hist G alg s r p`: the history of `p` after `r` rounds. -/
noncomputable def hist (s : Scenario P I M) : ℕ → P → History P M
  | 0, _ => []
  | r + 1, q => hist s r q ++ [fun p => deliver G alg s (hist s r) r p q]

@[simp] lemma hist_zero (s : Scenario P I M) (p : P) : hist G alg s 0 p = [] := rfl

lemma hist_succ (s : Scenario P I M) (r : ℕ) (q : P) :
    hist G alg s (r + 1) q =
      hist G alg s r q ++ [fun p => deliver G alg s (hist G alg s r) r p q] := rfl

@[simp] lemma length_hist (s : Scenario P I M) (r : ℕ) (p : P) : (hist G alg s r p).length = r := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih => simp [hist_succ, ih]

/-- The decision status of `p` after `r` rounds. -/
noncomputable def status (s : Scenario P I M) (r : ℕ) (p : P) : Option O :=
  alg.decide p (s.input p) (hist G alg s r p)

/-- `p`'s first decision in the run is `o`. -/
def Decides (s : Scenario P I M) (p : P) (o : O) : Prop :=
  ∃ r, status G alg s r p = some o ∧ ∀ r' < r, status G alg s r' p = none

/-- First decisions as a predicate on a status sequence (used to transfer decisions between
runs). -/
def FirstSome {O : Type*} (f : ℕ → Option O) (o : O) : Prop :=
  ∃ r, f r = some o ∧ ∀ r' < r, f r' = none

lemma FirstSome.unique {O : Type*} {f : ℕ → Option O} {o o' : O} (h : FirstSome f o)
    (h' : FirstSome f o') : o = o' := by
  obtain ⟨r, hr, hlt⟩ := h
  obtain ⟨r', hr', hlt'⟩ := h'
  rcases lt_trichotomy r r' with hrr | rfl | hrr
  · simp [hlt' r hrr] at hr
  · exact Option.some_injective _ (hr.symm.trans hr')
  · simp [hlt r' hrr] at hr'

lemma FirstSome.congr {O : Type*} {f g : ℕ → Option O} (hfg : ∀ r, f r = g r) {o : O} :
    FirstSome f o ↔ FirstSome g o := by
  simp [FirstSome, hfg]

lemma decides_iff_firstSome (s : Scenario P I M) (p : P) (o : O) :
    Decides G alg s p o ↔ FirstSome (fun r => status G alg s r p) o := Iff.rfl

lemma Decides.unique {s : Scenario P I M} {p : P} {o o' : O} (h : Decides G alg s p o)
    (h' : Decides G alg s p o') : o = o' := FirstSome.unique h h'

/-- Indistinguishability: if `p` has the same input and the same history at every round in two runs,
it makes the same decision. -/
lemma decides_congr {s s' : Scenario P I M} {p : P} (hx : s.input p = s'.input p)
    (hh : ∀ r, hist G alg s r p = hist G alg s' r p) (o : O) :
    Decides G alg s p o ↔ Decides G alg s' p o := by
  unfold Decides status
  simp [hx, hh]

/-- An *adversary structure*: the family of admissible Byzantine sets. -/
abbrev AdvStructure (P : Type*) := Set (Set P)

/-- A *problem specification*: a predicate on the inputs, the set of honest parties and the
(first-)decision relation of the run. -/
abbrev Spec (P I O : Type*) := (P → I) → Set P → (P → O → Prop) → Prop

/-- `alg` solves `spec` on network `G` against every admissible Byzantine set of `Z`
(reliable channels, unauthenticated adversary). -/
def Solves (Z : AdvStructure P) (spec : Spec P I O) : Prop :=
  ∀ s : Scenario P I M, s.byz ∈ Z → s.Reliable → spec s.input s.honest (Decides G alg s)

/-- A problem is *solvable* in the unauthenticated synchronous model on `G` against `Z` if some
protocol (with some message type) solves it. -/
def Solvable (G : SimpleGraph P) (Z : AdvStructure P) (spec : Spec P I O) : Prop :=
  ∃ (M : Type) (alg : Protocol P I M O), Solves G alg Z spec

/-! ### Changing the input format -/

/-- Run `alg` after translating the inputs with `f`. -/
def Protocol.comapInput {I' : Type*} (alg : Protocol P I M O) (f : I' → I) : Protocol P I' M O where
  send p x h q := alg.send p (f x) h q
  decide p x h := alg.decide p (f x) h

/-- Translate the inputs of a scenario. -/
def Scenario.mapInput {I' : Type*} (s : Scenario P I' M) (f : I' → I) : Scenario P I M :=
  { s with input := fun p => f (s.input p) }

lemma hist_comapInput {I' : Type*} (f : I' → I) (s : Scenario P I' M) :
    ∀ r, hist G (alg.comapInput f) s r = hist G alg (s.mapInput f) r := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    funext q
    rw [hist_succ, hist_succ, ih]
    rfl

lemma decides_comapInput {I' : Type*} (f : I' → I) (s : Scenario P I' M) (p : P) (o : O) :
    Decides G (alg.comapInput f) s p o ↔ Decides G alg (s.mapInput f) p o := by
  unfold Decides status
  simp only [hist_comapInput]
  rfl

end Cslib.Byzantine.LockStep
