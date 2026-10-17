/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Set.Card

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

Basic API: the threshold adversary structure `atMost t` (`≤ t` Byzantine parties); the honest
parties as a finset (`Scenario.honestFinset`); what a round delivers from honest / Byzantine
senders (`deliver_honest`, `deliver_byz`) and the inboxes of a history (`exists_of_mem_hist`,
`getElem?_hist`); histories depend only on the send function (`hist_eq_of_send_eq`); first
decisions (`firstSome_shift`, `firstSome_iff_of_ne`, `firstSome_iff_of_forall`,
`firstSome_map_iff`) and `firstSome?`, the first `some` value of a sequence; histories are
prefixes of each other (`take_hist`).

Indistinguishability tools:
* `hist_honest_congr`: the histories of the honest parties only depend on the honest inputs, the
  omissions between honest parties and the messages of Byzantine parties to honest neighbours.
* `padScenario G alg s Y`: declare the parties of `Y` Byzantine, but let them send exactly what they
  send in `s`. The run is unchanged (`hist_padScenario`, `status_padScenario`,
  `decides_padScenario`) and omissions of the padded parties disappear (`reliable_padScenario`).
  Used to reach an exact number of faults, or to turn omission faults into Byzantine ones.
* `decides_iff_of_hist`: a party that has decided within `k` rounds of `s₁` and has the same input
  and the same history after `k` rounds in `s₂` makes the same (first) decision in `s₂`.

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

/-! ### Threshold adversaries -/

section AtMost

/-- The threshold adversary structure: at most `t` Byzantine parties. -/
def atMost (t : ℕ) : AdvStructure P := {B | B.ncard ≤ t}

variable {t t' : ℕ} {B : Set P}

/-- Membership in the threshold structure. -/
@[simp] lemma mem_atMost : B ∈ (atMost t : AdvStructure P) ↔ B.ncard ≤ t := Iff.rfl

/-- A finset is admissible iff it has at most `t` elements. -/
lemma coe_mem_atMost (F : Finset P) : (F : Set P) ∈ (atMost t : AdvStructure P) ↔ F.card ≤ t := by
  simp [Set.ncard_coe_finset]

/-- The threshold structure grows with the threshold. -/
lemma atMost_mono (h : t ≤ t') : (atMost t : AdvStructure P) ⊆ atMost t' :=
  fun _ hB => le_trans hB h

/-- With threshold `0`, the only admissible set is `∅`. -/
lemma eq_empty_of_mem_atMost_zero [Finite P] (h : B ∈ (atMost 0 : AdvStructure P)) : B = ∅ :=
  (Set.ncard_eq_zero (Set.toFinite _)).1 (Nat.le_zero.1 h)

end AtMost

/-! ### Honest parties as a finset -/

section HonestFinset

variable [Fintype P] (s : Scenario P I M)

open Classical in
/-- The honest parties of a scenario, as a `Finset`. -/
noncomputable def Scenario.honestFinset : Finset P := Finset.univ.filter (· ∉ s.byz)

/-- Membership in `honestFinset`. -/
@[simp] lemma Scenario.mem_honestFinset {p : P} : p ∈ s.honestFinset ↔ p ∉ s.byz := by
  classical simp [Scenario.honestFinset]

/-- `honestFinset` as a set is `s.honest`. -/
@[simp] lemma Scenario.coe_honestFinset : (s.honestFinset : Set P) = s.honest := by
  ext p; simp [Scenario.honest]

/-- The number of honest parties is `n` minus the number of Byzantine parties. -/
lemma Scenario.card_honestFinset : s.honestFinset.card = Fintype.card P - s.byz.ncard := by
  classical
  rw [← Set.ncard_coe_finset, coe_honestFinset, Scenario.honest, Set.ncard_compl,
    Nat.card_eq_fintype_card]

/-- With at most `t` Byzantine parties, at least `n - t` parties are honest. -/
lemma Scenario.sub_le_card_honestFinset {t : ℕ} (h : s.byz.ncard ≤ t) :
    Fintype.card P - t ≤ s.honestFinset.card := by
  rw [card_honestFinset]; omega

end HonestFinset

/-! ### Histories and deliveries -/

section Hist

variable (s : Scenario P I M)

/-- A reliable link from an honest neighbour delivers the protocol message. -/
lemma deliver_honest (hrel : s.Reliable) {h : P → History P M} {r : ℕ} {q p : P}
    (hq : q ∉ s.byz) (hadj : G.Adj q p) :
    deliver G alg s h r q p = alg.send q (s.input q) (h q) p := by
  simp [deliver, hadj, hq, hrel r q p]

/-- A Byzantine neighbour delivers the adversary's message. -/
lemma deliver_byz {h : P → History P M} {r : ℕ} {q p : P} (hq : q ∈ s.byz) (hadj : G.Adj q p) :
    deliver G alg s h r q p = s.adv r q p := by
  simp [deliver, hadj, hq]

/-- An inbox occurring in a history is the inbox delivered in an earlier round. -/
lemma exists_of_mem_hist {r : ℕ} {p : P} {ib : Inbox P M} (h : ib ∈ hist G alg s r p) :
    ∃ r' < r, ib = fun q => deliver G alg s (hist G alg s r') r' q p := by
  induction r with
  | zero => simp at h
  | succ r ih =>
    rw [hist_succ, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · obtain ⟨r', hr', e⟩ := ih h; exact ⟨r', by omega, e⟩
    · exact ⟨r, by omega, rfl⟩

/-- The `k`-th inbox of a history is the inbox delivered in round `k`. -/
lemma getElem?_hist {k r : ℕ} (hk : k < r) (p : P) :
    (hist G alg s r p)[k]? = some (fun q => deliver G alg s (hist G alg s k) k q p) := by
  induction r with
  | zero => omega
  | succ r ih =>
    rw [hist_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [List.getElem?_append_left (by simpa using hk), ih hk]
    · rw [List.getElem?_append_right (by simp)]
      simp

/-- Histories only depend on the send function of the protocol. -/
lemma hist_eq_of_send_eq {O' : Type*} {alg' : Protocol P I M O'} (h : alg.send = alg'.send) :
    hist G alg s = hist G alg' s := by
  funext r
  induction r with
  | zero => rfl
  | succ r ih =>
    funext q
    rw [hist_succ, hist_succ, ih]
    simp only [deliver, h]

/-- The status under translated inputs is the status in the scenario with translated inputs. -/
lemma status_comapInput {I' : Type*} (f : I' → I) (s : Scenario P I' M) (r : ℕ) (p : P) :
    status G (alg.comapInput f) s r p = status G alg (s.mapInput f) r p := by
  simp only [status, hist_comapInput]; rfl

/-- Histories are prefixes of each other: the first `j` inboxes after `R ≥ j` rounds are the
history after `j` rounds. -/
lemma take_hist {j R : ℕ} (hj : j ≤ R) (p : P) :
    (hist G alg s R p).take j = hist G alg s j p := by
  induction R with
  | zero => rw [Nat.le_zero.1 hj]; rfl
  | succ R ih =>
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · rw [hist_succ, List.take_append_of_le_length (by simpa using Nat.lt_succ_iff.1 hj),
        ih (Nat.lt_succ_iff.1 hj)]
    · exact List.take_of_length_le (by simp)

end Hist

/-! ### First decisions -/

section FirstSome

variable {f : ℕ → Option O} {o : O}

/-- `FirstSome` after `n` silent steps. -/
lemma firstSome_shift (n : ℕ) (hf : ∀ r < n, f r = none) :
    FirstSome f o ↔ FirstSome (fun r => f (n + r)) o := by
  constructor
  · rintro ⟨r, hr, hlt⟩
    have hnr : n ≤ r := by by_contra h; rw [hf r (by omega)] at hr; simp at hr
    exact ⟨r - n, by simp [Nat.add_sub_cancel' hnr, hr], fun r' hr' => hlt _ (by omega)⟩
  · rintro ⟨r, hr, hlt⟩
    refine ⟨n + r, hr, fun r' hr' => ?_⟩
    rcases Nat.lt_or_ge r' n with h | h
    · exact hf r' h
    · have := hlt (r' - n) (by omega); simp only at this; rwa [Nat.add_sub_cancel' h] at this

/-- If `f` can only be `some` at step `r₀`, its first value is `f r₀`. -/
lemma firstSome_iff_of_ne (r₀ : ℕ) (hne : ∀ r, r ≠ r₀ → f r = none) :
    FirstSome f o ↔ f r₀ = some o := by
  constructor
  · rintro ⟨r, hr, -⟩
    by_cases h : r = r₀
    · rwa [h] at hr
    · rw [hne r h] at hr; cases hr
  · intro h; exact ⟨r₀, h, fun r hr => hne r (Nat.ne_of_lt hr)⟩

/-- A sequence that is `some v` from step `0` on has first value `v`. -/
lemma firstSome_iff_of_forall {v : O} (h : ∀ r, f r = some v) : FirstSome f o ↔ o = v := by
  constructor
  · rintro ⟨r, hr, -⟩; rw [h] at hr; exact (Option.some_injective _ hr).symm
  · rintro rfl; exact ⟨0, h 0, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- First values of a mapped sequence are images of first values. -/
lemma firstSome_map_iff {O' : Type*} {g : O → O'} {o' : O'} :
    FirstSome (fun r => (f r).map g) o' ↔ ∃ o, FirstSome f o ∧ g o = o' := by
  constructor
  · rintro ⟨r, hr, hlt⟩
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hr
    exact ⟨o, ⟨r, ho, fun r' h => Option.map_eq_none_iff.mp (hlt r' h)⟩, rfl⟩
  · rintro ⟨o, ⟨r, ho, hlt⟩, rfl⟩
    exact ⟨r, by simp [ho], fun r' h => by simp [hlt r' h]⟩

open Classical in
/-- The first `some` value of a sequence (`none` if there is none). -/
noncomputable def firstSome? (f : ℕ → Option O) : Option O :=
  if h : ∃ r, (f r).isSome then f (Nat.find h) else none

/-- `firstSome?` returns exactly the first `some` value. -/
lemma firstSome?_eq_some_iff : firstSome? f = some o ↔ FirstSome f o := by
  classical
  unfold firstSome?
  split_ifs with h
  · constructor
    · intro hx
      refine ⟨Nat.find h, hx, fun r' hr' => ?_⟩
      have := Nat.find_min h hr'
      simpa using this
    · rintro ⟨r, hr, hmin⟩
      rcases lt_or_eq_of_le (Nat.find_min' h (show (f r).isSome by simp [hr])) with hlt | heq
      · have := Nat.find_spec h
        rw [hmin _ hlt] at this
        simp at this
      · rw [heq, hr]
  · simp only [false_iff]
    rintro ⟨r, hr, -⟩
    exact h ⟨r, by simp [hr]⟩

/-- `firstSome?` is defined iff the sequence takes some `some` value. -/
lemma isSome_firstSome?_iff : (firstSome? f).isSome ↔ ∃ r, (f r).isSome := by
  classical
  unfold firstSome?
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => Nat.find_spec h⟩
  · simpa using h

end FirstSome

/-! ### Congruence of honest histories -/

/-- **Congruence of honest histories.** Two scenarios with the same Byzantine parties, the same
honest inputs, the same omissions between honest parties and the same messages from Byzantine
parties to honest neighbours give every honest party the same history. -/
theorem hist_honest_congr {s s' : Scenario P I M} (hbyz : s.byz = s'.byz)
    (hin : ∀ p ∉ s.byz, s.input p = s'.input p)
    (hdrop : ∀ r p q, p ∉ s.byz → q ∉ s.byz → G.Adj p q → (s.drop r p q ↔ s'.drop r p q))
    (hadv : ∀ r b q, b ∈ s.byz → q ∉ s.byz → G.Adj b q → s.adv r b q = s'.adv r b q) :
    ∀ r, ∀ p ∉ s.byz, hist G alg s r p = hist G alg s' r p := by
  intro r
  induction r with
  | zero => intro p _; rfl
  | succ r ih =>
    intro q hq
    rw [hist_succ, hist_succ, ih q hq]
    congr 1
    refine congrArg (fun f => [f]) (funext fun p => ?_)
    unfold deliver
    by_cases hadj : G.Adj p q
    · by_cases hp : p ∈ s.byz
      · simp [hadj, hp, ← hbyz, hadv r p q hp hq hadj]
      · have hd := hdrop r p q hp hq hadj
        by_cases h : s.drop r p q
        · simp [hadj, hp, ← hbyz, h, hd.1 h]
        · simp [hadj, hp, ← hbyz, h, mt hd.2 h, hin p hp, ih p hp]
    · simp [hadj]

/-! ### Padding: Byzantine parties that behave as in a given run -/

section Pad

open Classical in
/-- Declare the parties of `Y` Byzantine, but let them send exactly the messages they send as
(honest or Byzantine) parties in `s`. The run is unchanged (`hist_padScenario`). -/
noncomputable def padScenario (s : Scenario P I M) (Y : Set P) : Scenario P I M where
  byz := s.byz ∪ Y
  input := s.input
  adv r p q := if p ∈ s.byz then s.adv r p q
    else if s.drop r p q then none else alg.send p (s.input p) (hist G alg s r p) q
  drop r p q := s.drop r p q ∧ p ∉ Y

/-- Padding does not change the run. -/
theorem hist_padScenario (s : Scenario P I M) (Y : Set P) :
    ∀ r, hist G alg (padScenario G alg s Y) r = hist G alg s r := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    funext q
    rw [hist_succ, hist_succ, ih]
    congr 2
    funext p
    unfold deliver
    by_cases hp : p ∈ s.byz <;> by_cases hY : p ∈ Y <;> simp [padScenario, hp, hY]
    all_goals split_ifs <;> simp_all

/-- Omissions by the padded parties disappear: they are now Byzantine sends of nothing. -/
theorem reliable_padScenario {s : Scenario P I M} {Y : Set P}
    (h : ∀ r p q, s.drop r p q → p ∈ Y) : (padScenario G alg s Y).Reliable :=
  fun r p q hd => hd.2 (h r p q hd.1)

/-- Padding does not change the decision status. -/
theorem status_padScenario (s : Scenario P I M) (Y : Set P) (r : ℕ) (p : P) :
    status G alg (padScenario G alg s Y) r p = status G alg s r p := by
  simp only [status, hist_padScenario]
  rfl

/-- Padding does not change decisions. -/
theorem decides_padScenario (s : Scenario P I M) (Y : Set P) (p : P) (o : O) :
    Decides G alg (padScenario G alg s Y) p o ↔ Decides G alg s p o := by
  simp only [Decides, status_padScenario]

end Pad

/-! ### Decisions determined by a finite history -/

/-- A party that has decided within `k` rounds of `s₁` and has the same input and the same
history after `k` rounds in `s₂` makes the same (first) decision in `s₂`. -/
theorem decides_iff_of_hist {s₁ s₂ : Scenario P I M} {p : P} {k : ℕ}
    (hx : s₁.input p = s₂.input p) (hh : hist G alg s₁ k p = hist G alg s₂ k p)
    (hdec : ∃ r ≤ k, status G alg s₁ r p ≠ none) (o : O) :
    Decides G alg s₁ p o ↔ Decides G alg s₂ p o := by
  have hst : ∀ r ≤ k, status G alg s₁ r p = status G alg s₂ r p := by
    intro r hr
    simp only [status, hx, ← take_hist G alg s₁ hr p, ← take_hist G alg s₂ hr p, hh]
  obtain ⟨r₀, hr₀, hne⟩ := hdec
  constructor
  · rintro ⟨r, hr, hlt⟩
    have hrr : r ≤ r₀ := by
      by_contra h
      exact hne (hlt r₀ (by omega))
    exact ⟨r, (hst r (by omega)).symm ▸ hr, fun r' hr' => (hst r' (by omega)) ▸ hlt r' hr'⟩
  · rintro ⟨r, hr, hlt⟩
    have hrr : r ≤ r₀ := by
      by_contra h
      exact hne ((hst r₀ hr₀).trans (hlt r₀ (by omega)))
    exact ⟨r, (hst r (by omega)) ▸ hr, fun r' hr' => (hst r' (by omega)).trans (hlt r' hr')⟩

end Cslib.Byzantine.LockStep
