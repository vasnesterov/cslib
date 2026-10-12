/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Agreement.AttiyaWelch
public import Cslib.Computability.Distributed.Agreement.ReducingBroadcast

/-! # Reduced graded consensus: `O(n)` messages per process for every `t < n / 3`

The Attiya–Welch graded consensus AW′ (`Cslib.Distributed.AttiyaWelch.protocol`) echoes in its
first phase every value sent in `INIT` by more than `t` processes, i.e. up to `⌊n / (t + 1)⌋`
values, so that a process sends up to `n (⌊n / (t + 1)⌋ + 6)` messages
(`AttiyaWelch.bitsSent_one_le`): `O(n)` only if `n / (t + 1)` is bounded, e.g. for `n = 3t + 1`.
[Civit et al.][CivitEtAl2024] (appendix "Existing primitives") use AW with `O(n L)` bits per
process for every `t < n / 3`. We obtain this bound by putting a reducing broadcast
(`Cslib.Distributed.ReducingBroadcast`) in front of AW′, as the paper does for its validation
broadcast: the reducing broadcast realizes the paper's *reduction* to `O(1)` values for every
`t < n / 3`, which bounds the number of values that AW′ echoes.

**Protocol** (`protocol P Value t`): the composite (`Protocol.compose`) of a logic with two
children, the one-round reducing broadcast `ReducingBroadcast.protocol P Value t` (`rb`) and AW′
on values or `⊥_rd`, `AttiyaWelch.protocol P (Option Value) t` (`gc`). The logic
* upon its first `propose v`: broadcasts `v` via `rb`;
* upon `rb.deliver a`, `a : Option Value` (where `none` is `⊥_rd`), if it has proposed: proposes
  `a` to `gc`;
* upon `gc.decide a g`, unless it has decided: decides `(x, g)` if `a = some x`, and `(v, 0)` with
  its own proposal `v` if `a = ⊥_rd`;
* forwards `abandon` to both children.

**Guarantees** (for `3t < n`).
* It is a graded consensus protocol with latency `10δ = δ + 9δ` (`satisfies`): strong validity
  from the validity of `rb` and the strong validity of `gc`; external validity since a decided
  value `some x` of `gc` was proposed to `gc` by a correct process, hence delivered by it, hence
  broadcast by a correct process (safety of `rb`); consistency since a decision `(some x, 1)` of
  `gc` excludes every other decision value of `gc` at correct processes, including `⊥_rd`;
  latency `δ` of `rb` followed by latency `9δ` of `gc`.
* It is request-quiet (`requestQuiet`) and sends only between `propose` and `abandon`
  (`sendsWhileActive`).
* *Communication* (`card_sent_one_le`, `bitsSent_one_le`, `bitsSent_le`): in valid runs, a correct
  process sends at most `11 n` messages, and at most `11 n (L + 7)` bits for values of at most
  `L` bits, in every window of time. AW′ echoes at most five values in phase `1`: its `⊥`,
  `some ⊥_rd`, and at most three values `some (some y)`. Each of the latter has more than `t`
  recorded first `INIT`s (so there are at most `n / (t + 1)` of them), one from a correct process
  that delivered `some y`, so `y` was broadcast by `n - 3t` correct processes (so there are at
  most `n / (n - 3t)` of them, every process broadcasting once), and
  `min (n / (t + 1)) (n / (n - 3t)) ≤ 3` (`Quorum.card_le_three_of_pairwiseDisjoint`,
  `AttiyaWelch.card_sent_one_le_of_backed`).

## Implementation notes

* A decision `(⊥_rd, g)` of `gc` yields grade `0`, since different processes map `⊥_rd` to
  different values (their own proposals); it needs the own proposal, which a correct process has
  accepted by then: `gc` decides only after its proposal (`AttiyaWelch.decide_after_propose`),
  which follows a delivery of `rb`, which follows the broadcast (`isSome_prop_of_decide_gc`).
* The logic forwards a delivery to `gc` only once it has proposed. In valid runs, correct
  processes deliver only after broadcasting anyway; the gate makes the composite send only while
  active in every run (`gc` is started only after `propose`).
* The safety and latency proofs use the run-level lemmas of the two children (which need no
  environment assumption) on the projections of the run (`Run.child`); the logic makes each
  broadcast and each decision once (flags `prop` and `decided`).

## Main definitions

* `ReducedGradedConsensus.logic`, `ReducedGradedConsensus.children`,
  `ReducedGradedConsensus.protocol`: the logic, the children and the composite.
* `ReducedGradedConsensus.msgSize`: message sizes (one bit telling the children apart, followed by
  the message of the child).

## Main statements

* `ReducedGradedConsensus.satisfies`: for `3t < n`, the composite satisfies graded consensus with
  latency `10δ`.
* `ReducedGradedConsensus.requestQuiet`, `ReducedGradedConsensus.sendsWhileActive`.
* `ReducedGradedConsensus.card_sent_one_le`: AW′ echoes at most five values in phase `1`.
* `ReducedGradedConsensus.bitsSent_one_le`, `ReducedGradedConsensus.bitsSent_le`: a correct
  process sends at most `11 n` messages and `11 n (L + 7)` bits, for every `t < n / 3`.
* `ReducedGradedConsensus.bitsSent_one_le_div`, `ReducedGradedConsensus.bitsSent_le_div`: in
  every run, whatever the number of faulty processes, a process sends at most `n (n / (t + 1) + 7)`
  messages and `n (n / (t + 1) + 7) (L + 7)` bits;
  `ReducedGradedConsensus.bitsSent_one_le_of_card_le`,
  `ReducedGradedConsensus.bitsSent_le_of_card_le`: `10 n` messages and `10 n (L + 7)` bits if
  `n ≤ 3 (t + 1)`.

## References

* [P. Civit, M. A. Dzulfikar, S. Gilbert, R. Guerraoui, J. Komatovic, M. Vidigueira,
  I. Zablotchi, *Partial Synchrony for Free? New Upper Bounds for Byzantine Agreement*,
  arXiv:2402.10059][CivitEtAl2024]
* [A. Mostéfaoui, M. Raynal, *Signature-Free Asynchronous Byzantine Systems: From Multivalued to
  Binary Consensus with t < n/3, O(n²) Messages, and Constant Time*, Acta Informatica 54(5),
  2017][MostefaouiRaynal2017]
* [H. Attiya, J. L. Welch, *Multi-Valued Connected Consensus: A New Perspective on Crusader
  Agreement and Adopt-Commit*, OPODIS 2023][AttiyaWelch2023]
-/

@[expose] public section

namespace Cslib.Distributed.ReducedGradedConsensus

open GradedConsensus Finset

/-! ### The logic -/

/-- The children of the composite: a reducing broadcast on values (`rb`) and a graded consensus
on values or `⊥_rd` (`gc`). -/
inductive Child where
  /-- The reducing broadcast. -/
  | rb
  /-- The graded consensus on `Option Value`. -/
  | gc
deriving DecidableEq

instance : Fintype Child := ⟨{.rb, .gc}, fun i => by cases i <;> simp⟩

/-- A sum over the children. -/
theorem Child.sum_univ {M : Type*} [AddCommMonoid M] (f : Child → M) :
    ∑ i, f i = f .rb + f .gc :=
  Finset.sum_pair (by decide)

/-- The interfaces of the children. -/
abbrev Child.interface (Value : Type) : Child → Interface
  | .rb => ReducingBroadcast.interface Value
  | .gc => GradedConsensus.interface (Option Value)

/-- The interface of the logic: graded consensus, extended with the children's interfaces. -/
abbrev logicInterface (Value : Type) : Interface :=
  (GradedConsensus.interface Value).uses (Child.interface Value)

/-- The requests of the logic (`(logicInterface Value).Req`, unfolded): the requests of graded
consensus and the indications of the children. -/
abbrev LReq (Value : Type) : Type := Req Value ⊕ Σ i, (Child.interface Value i).Ind

/-- The indications of the logic (`(logicInterface Value).Ind`, unfolded): the indications of
graded consensus and the requests to the children. -/
abbrev LInd (Value : Type) : Type := Ind Value ⊕ Σ i, (Child.interface Value i).Req

namespace Logic

/-- The inputs of the logic (it has no messages and no timers). -/
abbrev In (P Value : Type) := Input P Empty Empty (LReq Value)

/-- The outputs of the logic. -/
abbrev Out (P Value : Type) := Output P Empty Empty (LInd Value)

/-- The local state of the logic. -/
structure State (Value : Type) where
  /-- The own proposal, once accepted. -/
  prop : Option Value
  /-- The process has decided. -/
  decided : Bool

/-- The initial state of the logic. -/
def State.init {Value : Type} : State Value := ⟨none, false⟩

variable {P Value : Type}

/-- The decision taken upon the decision `(a, g)` of the graded consensus on `Option Value`,
given the own proposal `prop`: `(x, g)` if `a = some x`; `(v, 0)` with the own proposal `v` if
`a = ⊥_rd`, if there is one. -/
def decision (prop : Option Value) : Option Value → Bool → Option (Value × Bool)
  | some x, g => some (x, g)
  | none, _ => prop.map (·, false)

/-- The step function of the logic.
* `propose v`: unless the process has already proposed, accept `v` and broadcast it via the
  reducing broadcast.
* `abandon`: abandon both children.
* `deliver a` (reducing broadcast): if the process has proposed, propose `a` to the graded
  consensus on `Option Value`.
* `decide a g` (graded consensus on `Option Value`): unless the process has decided, decide
  `decision prop a g`, if any. -/
def step : In P Value → State Value → State Value × List (Out P Value)
  | .req (.inl (.propose v)), s =>
    if s.prop.isSome then (s, [])
    else ({ s with prop := some v }, [.ind (.inr ⟨.rb, .broadcast v⟩)])
  | .req (.inl .abandon), s => (s, [.ind (.inr ⟨.rb, .abandon⟩), .ind (.inr ⟨.gc, .abandon⟩)])
  | .req (.inr ⟨.rb, .deliver a⟩), s =>
    if s.prop.isSome then (s, [.ind (.inr ⟨.gc, .propose a⟩)]) else (s, [])
  | .req (.inr ⟨.gc, .decide a g⟩), s =>
    if s.decided then (s, [])
    else ({ s with decided := (decision s.prop a g).isSome },
      (decision s.prop a g).toList.map fun d => .ind (.inl (.decide d.1 d.2)))
  | .recv _ m, _ => m.elim
  | .timeout k, _ => k.elim

end Logic

variable (P Value : Type)

/-- The **logic** of the reduced graded consensus. -/
abbrev logic : Protocol P (logicInterface Value) where
  Msg := Empty
  Timer := Empty
  State := Logic.State Value
  init _ := .init
  step _ _ x s := Logic.step x s

/-- The children: the one-round reducing broadcast and AW′ on `Option Value`. -/
noncomputable abbrev children [Fintype P] [DecidableEq P] [DecidableEq Value] (t : ℕ) :
    (i : Child) → Protocol P (Child.interface Value i)
  | .rb => ReducingBroadcast.protocol P Value t
  | .gc => AttiyaWelch.protocol P (Option Value) t

/-- **The reduced graded consensus protocol**. -/
noncomputable abbrev protocol [Fintype P] [DecidableEq P] [DecidableEq Value] (t : ℕ) :
    Protocol P (GradedConsensus.interface Value) :=
  (logic P Value).compose (children P Value t)

variable {P Value}

/-! ### Steps of the logic -/

namespace Logic

variable {x : In P Value} {s : State Value} {v w : Value} {a : Option Value} {g : Bool}

/-- Case analysis on the inputs of the logic. -/
local macro "step_cases" x:ident : tactic => `(tactic|
  (rcases $x:ident with ((_ | _) | ⟨_ | _, r⟩) | ⟨_, ⟨⟩⟩ | ⟨⟨⟩⟩ <;> try cases r))

/-- An accepted proposal is never changed. -/
theorem prop_step_of_eq_some (h : s.prop = some v) : (step x s).1.prop = some v := by
  step_cases x <;> simp only [step] <;> (try split) <;> simp_all

/-- A proposal is accepted only upon `propose`. -/
theorem prop_step_eq_some (h : (step x s).1.prop = some v) :
    s.prop = some v ∨ x = .req (.inl (.propose v)) := by
  step_cases x <;> simp only [step] at h <;> (try split at h) <;> simp_all

theorem isSome_prop_step (h : s.prop.isSome) : (step x s).1.prop.isSome := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  rw [prop_step_of_eq_some hv]
  rfl

/-- The flag `decided` is never reset. -/
theorem decided_step (h : s.decided = true) : (step x s).1.decided = true := by
  step_cases x <;> simp only [step] <;> (try split) <;> simp_all

/-- The logic broadcasts `v` upon `propose v` if it has not accepted a proposal yet. -/
theorem broadcast_mem_step :
    .ind (.inr ⟨.rb, .broadcast v⟩) ∈ (step x s).2 ↔
      x = .req (.inl (.propose v)) ∧ s.prop = none := by
  step_cases x <;> simp only [step] <;> (try split) <;>
    simp_all [eq_comm (a := v), Option.isSome_iff_ne_none]

/-- `abandon` is forwarded to the reducing broadcast. -/
theorem abandon_rb_mem_step :
    .ind (.inr ⟨.rb, .abandon⟩) ∈ (step x s).2 ↔ x = .req (.inl .abandon) := by
  step_cases x <;> simp only [step] <;> (try split) <;> simp_all

/-- `abandon` is forwarded to the graded consensus on `Option Value`. -/
theorem abandon_gc_mem_step :
    .ind (.inr ⟨.gc, .abandon⟩) ∈ (step x s).2 ↔ x = .req (.inl .abandon) := by
  step_cases x <;> simp only [step] <;> (try split) <;> simp_all

/-- The logic proposes `a` to the graded consensus on `Option Value` upon delivering `a`, if it
has accepted a proposal. -/
theorem propose_gc_mem_step :
    .ind (.inr ⟨.gc, .propose a⟩) ∈ (step x s).2 ↔
      x = .req (.inr ⟨.rb, .deliver a⟩) ∧ s.prop.isSome := by
  step_cases x <;> simp only [step] <;> (try split) <;> simp_all [eq_comm (a := a)]

/-- The logic decides `(w, g)` upon a decision `(a, g')` of the graded consensus on
`Option Value` with `decision prop a g' = some (w, g)`, unless it has decided. -/
theorem decide_mem_step :
    .ind (.inl (.decide w g)) ∈ (step x s).2 ↔
      ∃ a g', x = .req (.inr ⟨.gc, .decide a g'⟩) ∧ s.decided = false ∧
        decision s.prop a g' = some (w, g) := by
  step_cases x <;> simp only [step] <;> (try split) <;> simp_all [-Bool.exists_bool]

/-- A step that sets the flag `decided` decides. -/
theorem decided_step_eq_true (h : (step x s).1.decided = true) :
    s.decided = true ∨ ∃ w g, .ind (.inl (.decide w g)) ∈ (step x s).2 := by
  step_cases x <;> simp only [step] at h ⊢ <;> (try split) <;>
    simp_all [Option.isSome_iff_exists]

/-- The decisions of the logic, as outputs. -/
def isDecide (o : Out P Value) : Bool := o matches .ind (.inl _)

/-- A step that decides decides once, and sets the flag `decided`, which was not set. -/
theorem countP_decide_step (h : 0 < (step x s).2.countP isDecide) :
    s.decided = false ∧ (step x s).1.decided = true ∧ (step x s).2.countP isDecide ≤ 1 := by
  step_cases x <;> simp only [step] at h ⊢ <;> (try split) <;>
    simp_all [isDecide, Option.isSome_iff_exists, -Bool.exists_bool,
      List.countP_le_length.trans Option.length_toList_le]

/-- The broadcasts of the logic via the reducing broadcast, as outputs. -/
def isBroadcast (o : Out P Value) : Bool := o matches .ind (.inr ⟨.rb, .broadcast _⟩)

/-- A step that broadcasts broadcasts once, and accepts a proposal, which was not accepted. -/
theorem countP_broadcast_step (h : 0 < (step x s).2.countP isBroadcast) :
    s.prop.isSome = false ∧ (step x s).1.prop.isSome ∧ (step x s).2.countP isBroadcast ≤ 1 := by
  step_cases x <;> simp only [step] at h ⊢ <;> (try split) <;> simp_all [isBroadcast]

end Logic

/-- The logic is parent-request-quiet: `propose` and `abandon` only emit requests to the
children. -/
theorem Logic.parentRequestQuiet : (logic P Value).ParentRequestQuiet := by
  rintro p now (v | _) s i hi <;> simp only [logic, Logic.step] at hi <;> (try split at hi) <;>
    simp at hi

/-! ### Runs of the logic -/

namespace Logic

variable {σ : Run (logic P Value)} {p : P} {τ T : ℕ} {v w : Value} {a : Option Value} {g : Bool}

/-- *At most one broadcast*: in every run, a process broadcasts at most once via the reducing
broadcast (the proposal is accepted once). -/
theorem atMostOnce_broadcast (σ : Run (logic P Value)) (p : P) :
    σ.history.AtMostOnce p fun e => e.ind?.any fun i => isBroadcast (P := P) (.ind i) :=
  Run.atMostOnce_of_flag_output (c := isBroadcast) (fun _ => rfl)
    (fun o => by rcases o with ⟨_, ⟨⟩⟩ | i | ⟨⟨⟩, _⟩; rfl)
    (fun s : State Value => s.prop.isSome = true) (by simp [State.init])
    (fun _ _ _ => isSome_prop_step) fun _ _ _ h => by
      obtain ⟨h₁, h₂, h₃⟩ := countP_broadcast_step h
      exact ⟨by simp [h₁], h₂, h₃⟩

/-- A process broadcasts at most one value via the reducing broadcast. -/
theorem eq_of_broadcast {τ' : ℕ} (h : .ind (.inr ⟨.rb, .broadcast v⟩) ∈ σ.output p τ)
    (h' : .ind (.inr ⟨.rb, .broadcast w⟩) ∈ σ.output p τ') : v = w := by
  have := ((atMostOnce_broadcast σ p).eq_of_mem (Run.ind_mem_trace.2 h) (Run.ind_mem_trace.2 h')
    rfl rfl).2
  simpa using this

/-- *Integrity*: in every run, a process decides at most once (flag `decided`). -/
theorem atMostOnce_decide (σ : Run (logic P Value)) (p : P) :
    σ.history.AtMostOnce p (· matches .ind (.inl _)) :=
  Run.atMostOnce_of_flag_output (c := isDecide) (fun _ => rfl)
    (fun o => by rcases o with ⟨_, ⟨⟩⟩ | (_ | _) | ⟨⟨⟩, _⟩ <;> rfl)
    (fun s : State Value => s.decided = true) (by simp [State.init])
    (fun _ _ _ => decided_step) fun _ _ _ h => by
      obtain ⟨h₁, h₂, h₃⟩ := countP_decide_step h
      exact ⟨by simp [h₁], h₂, h₃⟩

/-- An accepted proposal stays accepted. -/
theorem isSome_prop_mono {τ' : ℕ} (h : (σ.state p τ).prop.isSome) (hτ : τ ≤ τ') :
    (σ.state p τ').prop.isSome :=
  Run.state_of_stable (ρ := σ) (Q := fun s : State Value => s.prop.isSome = true)
    (fun _ _ _ => isSome_prop_step) h hτ

/-- A process that has accepted a proposal handled a `propose` request earlier. -/
theorem exists_propose_of_isSome_prop (h : (σ.state p T).prop.isSome) :
    ∃ τ < T, ∃ v, .req (.inl (.propose v)) ∈ σ.input p τ := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨τ, hτ, x, hx, rfl⟩ := Run.exists_input_of_state (ρ := σ)
    (Q := fun s : State Value => s.prop = some v)
    (g := fun x : In P Value => x = .req (.inl (.propose v))) (by simp [State.init])
    (fun _ _ _ h => prop_step_eq_some h) hv
  exact ⟨τ, hτ, v, hx⟩

/-- A process that has accepted a proposal broadcast via the reducing broadcast earlier. -/
theorem exists_broadcast_of_isSome_prop (h : (σ.state p T).prop.isSome) :
    ∃ τ < T, ∃ v, .ind (.inr ⟨.rb, .broadcast v⟩) ∈ σ.output p τ := by
  obtain ⟨τ, hτ, o, ho, v, rfl⟩ := Run.exists_output_of_state (ρ := σ)
    (Q := fun s : State Value => s.prop.isSome = true)
    (O := fun o => ∃ v, o = .ind (.inr ⟨.rb, .broadcast v⟩)) (by simp [State.init])
    (fun _ x s h => by
      cases hs : s.prop with
      | some _ => exact .inl rfl
      | none =>
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
        rcases prop_step_eq_some hv with h' | rfl
        · simp [hs] at h'
        · exact .inr ⟨_, broadcast_mem_step.2 ⟨rfl, hs⟩, v, rfl⟩) h
  exact ⟨τ, hτ, v, ho⟩

/-- After handling `propose`, a process has accepted a proposal. -/
theorem isSome_prop_of_propose (h : .req (.inl (.propose v)) ∈ σ.input p τ) :
    (σ.state p (τ + 1)).prop.isSome := by
  obtain ⟨s, hs⟩ := Run.exists_handles_of_mem_input h
  refine hs.state_of_stable (Q := fun s : State Value => s.prop.isSome = true)
    (fun _ _ _ => isSome_prop_step) ?_ (Nat.lt_succ_self τ)
  simp only [logic, step]
  split <;> simp_all

/-- A process broadcasts via the reducing broadcast only upon `propose`. -/
theorem propose_of_broadcast (h : .ind (.inr ⟨.rb, .broadcast v⟩) ∈ σ.output p τ) :
    .req (.inl (.propose v)) ∈ σ.input p τ := by
  obtain ⟨x, s, hs, hx⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨rfl, -⟩ := broadcast_mem_step.1 hx
  exact hs.mem_input

/-- A process proposes to the graded consensus on `Option Value` only upon a delivery of the
reducing broadcast. -/
theorem deliver_of_propose_gc (h : .ind (.inr ⟨.gc, .propose a⟩) ∈ σ.output p τ) :
    .req (.inr ⟨.rb, .deliver a⟩) ∈ σ.input p τ := by
  obtain ⟨x, s, hs, hx⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨rfl, -⟩ := propose_gc_mem_step.1 hx
  exact hs.mem_input

/-- A process proposes to the graded consensus on `Option Value` only once it has accepted a
proposal. -/
theorem isSome_prop_of_propose_gc (h : .ind (.inr ⟨.gc, .propose a⟩) ∈ σ.output p τ) :
    (σ.state p (τ + 1)).prop.isSome :=
  Run.state_of_mem_output (ρ := σ) (Q := fun s : State Value => s.prop.isSome = true)
    (fun _ _ _ => isSome_prop_step)
    (fun _ _ _ h => isSome_prop_step (propose_gc_mem_step.1 h).2) h (Nat.lt_succ_self τ)

/-- A process proposes to the graded consensus on `Option Value` only after its own
`propose`. -/
theorem exists_propose_of_propose_gc (h : .ind (.inr ⟨.gc, .propose a⟩) ∈ σ.output p τ) :
    ∃ τ' ≤ τ, ∃ v, .req (.inl (.propose v)) ∈ σ.input p τ' := by
  obtain ⟨τ', hτ', v, h'⟩ := exists_propose_of_isSome_prop (isSome_prop_of_propose_gc h)
  exact ⟨τ', by omega, v, h'⟩

/-- A process that has accepted a proposal forwards a delivery of the reducing broadcast to the
graded consensus on `Option Value`. -/
theorem propose_gc_of_deliver (h : .req (.inr ⟨.rb, .deliver a⟩) ∈ σ.input p τ)
    (hp : (σ.state p τ).prop.isSome) : .ind (.inr ⟨.gc, .propose a⟩) ∈ σ.output p τ := by
  obtain ⟨s, hs⟩ := Run.exists_handles_of_mem_input h
  exact hs.mem_output (propose_gc_mem_step.2 ⟨rfl, hs.of_inputs
    (Q := fun s : State Value => s.prop.isSome = true) (fun _ _ _ h => isSome_prop_step h) hp⟩)

/-- `abandon` is forwarded to the reducing broadcast. -/
theorem abandon_rb_iff :
    .ind (.inr ⟨.rb, .abandon⟩) ∈ σ.output p τ ↔ .req (.inl .abandon) ∈ σ.input p τ :=
  ⟨fun h => let ⟨_, _, hs, hx⟩ := Run.mem_output_iff_handles.1 h
      abandon_rb_mem_step.1 hx ▸ hs.mem_input,
    fun h => Run.mem_output_of_mem_input h fun _ => abandon_rb_mem_step.2 rfl⟩

/-- `abandon` is forwarded to the graded consensus on `Option Value`. -/
theorem abandon_gc_iff :
    .ind (.inr ⟨.gc, .abandon⟩) ∈ σ.output p τ ↔ .req (.inl .abandon) ∈ σ.input p τ :=
  ⟨fun h => let ⟨_, _, hs, hx⟩ := Run.mem_output_iff_handles.1 h
      abandon_gc_mem_step.1 hx ▸ hs.mem_input,
    fun h => Run.mem_output_of_mem_input h fun _ => abandon_gc_mem_step.2 rfl⟩

/-- A decision `(w, g)` comes from a decision `(some w, g)` of the graded consensus on
`Option Value`, or from a decision `(⊥_rd, ·)`, with grade `0` and the own proposal `w`. -/
theorem decide_gc_of_decide (h : .ind (.inl (.decide w g)) ∈ σ.output p τ) :
    .req (.inr ⟨.gc, .decide (some w) g⟩) ∈ σ.input p τ ∨
      (g = false ∧ (∃ g', .req (.inr ⟨.gc, .decide none g'⟩) ∈ σ.input p τ) ∧
        ∃ τ' ≤ τ, .req (.inl (.propose w)) ∈ σ.input p τ') := by
  obtain ⟨x, s, hs, hx⟩ := Run.mem_output_iff_handles.1 h
  obtain ⟨a, g', rfl, -, hd⟩ := decide_mem_step.1 hx
  cases a with
  | some y =>
    cases hd
    exact .inl hs.mem_input
  | none =>
    simp only [decision, Option.map_eq_some_iff, Prod.mk.injEq] at hd
    obtain ⟨w', hw, hw', rfl⟩ := hd
    rw [hw'] at hw
    obtain ⟨τ', hτ', y, hy, rfl⟩ := hs.exists_input
      (Q := fun s : State Value => s.prop = some w)
      (g := fun y : In P Value => y = .req (.inl (.propose w)))
      (by simp [State.init]) (fun _ _ _ h => prop_step_eq_some h) hw
    exact .inr ⟨rfl, ⟨g', hs.mem_input⟩, τ', hτ', hy⟩

/-- A process that has accepted a proposal decides upon a decision of the graded consensus on
`Option Value`, unless it has decided earlier. -/
theorem exists_decide_of_decide_gc (h : .req (.inr ⟨.gc, .decide a g⟩) ∈ σ.input p τ)
    (hp : (σ.state p τ).prop.isSome) :
    ∃ τ' ≤ τ, ∃ w g, .ind (.inl (.decide w g)) ∈ σ.output p τ' := by
  obtain ⟨s, hs⟩ := Run.exists_handles_of_mem_input h
  have hps : s.prop.isSome := hs.of_inputs (Q := fun s : State Value => s.prop.isSome = true)
    (fun _ _ _ h => isSome_prop_step h) hp
  -- the flag `decided` is set after handling the decision
  have hd : (σ.state p (τ + 1)).decided = true := by
    refine hs.state_of_stable (Q := fun s : State Value => s.decided = true)
      (fun _ _ _ => decided_step) ?_ (Nat.lt_succ_self τ)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hps
    simp only [logic, step]
    split
    · assumption
    · cases a <;> simp [decision, hv]
  obtain ⟨τ', hτ', o, ho, w, g, rfl⟩ := Run.exists_output_of_state (ρ := σ)
    (Q := fun s : State Value => s.decided = true)
    (O := fun o => ∃ w g, o = .ind (.inl (.decide w g))) (by simp [State.init])
    (fun _ _ _ h => (decided_step_eq_true h).imp_right fun ⟨w, g, h⟩ => ⟨_, h, w, g, rfl⟩) hd
  exact ⟨τ', by omega, w, g, ho⟩

end Logic

/-! ### The composite -/

section Composite

variable [Fintype P] [DecidableEq P] [DecidableEq Value]

/-- **The reduced graded consensus is request-quiet**: handling `propose` or `abandon` never emits
an indication. -/
theorem requestQuiet (t : ℕ) : (protocol P Value t).RequestQuiet :=
  Protocol.requestQuiet_compose Logic.parentRequestQuiet

variable (P Value) in
/-- The children are request-quiet. -/
theorem children_requestQuiet (t : ℕ) : ∀ i, (children P Value t i).RequestQuiet
  | .rb => ReducingBroadcast.requestQuiet t
  | .gc => AttiyaWelch.requestQuiet t

/-- **Integrity**: in every run, a process decides at most once. -/
theorem atMostOnce {t : ℕ} (ρ : Run (protocol P Value t)) (p : P) :
    ρ.history.AtMostOnce p (· matches .ind _) :=
  (Logic.atMostOnce_decide ρ.logic p).of_countP_trace_le fun τ => by
    rw [Run.history_trace, Run.history_trace, Run.trace_compose, List.countP_filterMap]
    refine le_of_eq (List.countP_congr fun e _ => ?_)
    rcases e with (_ | _) | (_ | _) <;> simp [Event.parent?]

/-- **The reduced graded consensus sends only while active**: a process sends messages only from
its `propose` on and never after its `abandon`, since the reducing broadcast and AW′ do so with
respect to their own start requests and `abandon`, the logic makes these start requests only
after `propose`, and it forwards `abandon` to both. -/
theorem sendsWhileActive (t : ℕ) :
    (protocol P Value t).SendsWhileActive (· matches .propose _) (· matches .abandon) := by
  intro ρ p τ q m h
  -- `abandon` reaches both children at once
  have hstop : ∀ τ', .req .abandon ∈ ρ.input p τ' → .req (.inl .abandon) ∈ ρ.logic.input p τ' :=
    fun τ' h => Run.history_reqAt_compose.1 (Run.history_reqAt.2 h)
  rcases m with ⟨⟨⟩⟩ | ⟨i, m⟩
  cases i with
  | rb =>
    obtain ⟨⟨τ', hτ', r, hr, hreq⟩, hstop'⟩ := ReducingBroadcast.sendsWhileActive t (ρ.child .rb)
      p τ q m (Run.send_mem_output_child.2 h)
    rcases r with v | _
    · refine ⟨⟨τ', hτ', .propose v, rfl, Run.history_reqAt.1 (Run.history_reqAt_compose.2
        (Logic.propose_of_broadcast (Run.req_mem_input_child.1 hreq)))⟩, ?_⟩
      rintro τ'' hτ'' (_ | _) hr' hin
      · cases hr'
      · exact hstop' τ'' hτ'' .abandon rfl
          (Run.req_mem_input_child.2 (Logic.abandon_rb_iff.2 (hstop τ'' hin)))
    · cases hr
  | gc =>
    obtain ⟨⟨τ', hτ', r, hr, hreq⟩, hstop'⟩ := AttiyaWelch.sendsWhileActive t (ρ.child .gc)
      p τ q m (Run.send_mem_output_child.2 h)
    rcases r with a | _
    · obtain ⟨τ'', hτ'', v, hv⟩ := Logic.exists_propose_of_propose_gc
        (Run.req_mem_input_child.1 hreq)
      refine ⟨⟨τ'', hτ''.trans hτ', .propose v, rfl,
        Run.history_reqAt.1 (Run.history_reqAt_compose.2 hv)⟩, ?_⟩
      rintro τ'' hτ'' (_ | _) hr' hin
      · cases hr'
      · exact hstop' τ'' hτ'' .abandon rfl
          (Run.req_mem_input_child.2 (Logic.abandon_gc_iff.2 (hstop τ'' hin)))
    · cases hr

/-! #### Valid runs -/

variable {t δ : ℕ} {ρ : Run (protocol P Value t)} {p : P} {τ : ℕ} {v w : Value}
  {a : Option Value} {g : Bool}

/-- A process proposes `a` to AW′ only upon delivering `a` (in every run). -/
theorem deliver_of_propose_gc (h : .req (.propose a) ∈ (ρ.child .gc).input p τ) :
    .ind (.deliver a) ∈ (ρ.child .rb).output p τ :=
  (Run.ind_mem_output_child (children_requestQuiet P Value t .rb)).2
    (Logic.deliver_of_propose_gc (Run.req_mem_input_child.1 h))

/-- If a correct process delivers `some w`, some correct process proposed `w` earlier (safety of
the reducing broadcast, with `n - 3t > 0` correct broadcasters of `w`). -/
theorem exists_propose_of_deliver (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    (hp : p ∉ ρ.faulty) (h : .ind (.deliver (some w)) ∈ (ρ.child .rb).output p τ) :
    ∃ q ∉ ρ.faulty, ∃ τ' < τ, .req (.inl (.propose w)) ∈ ρ.logic.input q τ' := by
  obtain ⟨S, hS, hS'⟩ := ReducingBroadcast.safety (hρ.child .rb) hp h
  obtain ⟨q, hq⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨hqF, τ', hτ', h'⟩ := hS' q hq
  exact ⟨q, hqF, τ', hτ', Logic.propose_of_broadcast (Run.req_mem_input_child.1 h')⟩

/-- A correct process delivers only after it has accepted a proposal. -/
theorem isSome_prop_of_deliver (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty)
    (h : .ind (.deliver a) ∈ (ρ.child .rb).output p τ) : (ρ.logic.state p τ).prop.isSome := by
  obtain ⟨τ', hτ', v, h'⟩ := ReducingBroadcast.afterBroadcast (hρ.child .rb) hp h
  exact Logic.isSome_prop_mono
    (Logic.isSome_prop_of_propose (Logic.propose_of_broadcast (Run.req_mem_input_child.1 h')))
    (by omega)

/-- A correct process's AW′ decides only after it has accepted a proposal. -/
theorem isSome_prop_of_decide_gc (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty)
    (h : .ind (.decide a g) ∈ (ρ.child .gc).output p τ) : (ρ.logic.state p τ).prop.isSome := by
  obtain ⟨b, τ', hτ', h'⟩ := AttiyaWelch.decide_after_propose (hρ.child .gc) hp h
  exact Logic.isSome_prop_mono (Logic.isSome_prop_of_propose_gc (Run.req_mem_input_child.1 h'))
    (by omega)

/-! #### Safety -/

/-- **Strong validity**: if all correct processes that propose do so with `v`, every decision of a
correct process is `(v, 1)`. All correct broadcasts carry `v`, so every correct delivery is
`some v` (validity of the reducing broadcast), hence every correct proposal to AW′ is `some v`, and
AW′ decides `(some v, 1)` (strong validity of AW′). -/
theorem strongValidity (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    (hU : ∀ q ∉ ρ.faulty, ∀ w τ, .req (.inl (.propose w)) ∈ ρ.logic.input q τ → w = v)
    (hp : p ∉ ρ.faulty) (h : .ind (.inl (.decide w g)) ∈ ρ.logic.output p τ) :
    w = v ∧ g = true := by
  have hgc : AttiyaWelch.Unanimous (ρ.child .gc) (some v) := fun q hq a τ h =>
    ReducingBroadcast.validity (hρ.child .rb) hn
      (fun r hr w τ h => hU r hr w τ (Logic.propose_of_broadcast (Run.req_mem_input_child.1 h))) hq
      (deliver_of_propose_gc h)
  have hdec := fun {a g} (h : .req (.inr ⟨.gc, .decide a g⟩) ∈ ρ.logic.input p τ) =>
    AttiyaWelch.unanimity_decide (hρ.child .gc) hn hgc hp
      ((Run.ind_mem_output_child (children_requestQuiet P Value t .gc)).2 h)
  rcases Logic.decide_gc_of_decide h with h' | ⟨-, ⟨g', h'⟩, -⟩
  · obtain ⟨hw, hg⟩ := hdec h'
    exact ⟨Option.some.inj hw, hg⟩
  · exact absurd (hdec h').1 (by simp)

/-- **Proposal validity**: a value decided by a correct process was proposed by a correct
process. A decision `(some w, ·)` of AW′ was proposed to AW′ by a correct process (proposal
validity of AW′), hence delivered by it, hence broadcast by a correct process (safety of the
reducing broadcast); a decision `(⊥_rd, ·)` is mapped to the own proposal. -/
theorem exists_propose_of_decide (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    (hp : p ∉ ρ.faulty) (h : .ind (.inl (.decide w g)) ∈ ρ.logic.output p τ) :
    ∃ q ∉ ρ.faulty, ∃ τ', .req (.inl (.propose w)) ∈ ρ.logic.input q τ' := by
  rcases Logic.decide_gc_of_decide h with h' | ⟨-, -, τ', -, h'⟩
  · obtain ⟨q, hq, τ', h''⟩ := AttiyaWelch.proposal_validity (hρ.child .gc) hn hp
      ((Run.ind_mem_output_child (children_requestQuiet P Value t .gc)).2 h')
    obtain ⟨r, hr, τ'', -, h'''⟩ := exists_propose_of_deliver hρ hn hq (deliver_of_propose_gc h'')
    exact ⟨r, hr, τ'', h'''⟩
  · exact ⟨p, hp, τ', h'⟩

/-- **Consistency**: if a correct process decides `(v, 1)`, every decision of a correct process has
value `v`. A grade-`1` decision `(v, 1)` comes from a decision `(some v, 1)` of AW′, which
excludes every other decision value of AW′ at correct processes, in particular `⊥_rd`
(consistency of AW′). -/
theorem consistency (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P) {q : P} {τ' : ℕ}
    (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty) (h₁ : .ind (.inl (.decide v true)) ∈ ρ.logic.output p τ)
    (h₂ : .ind (.inl (.decide w g)) ∈ ρ.logic.output q τ') : w = v := by
  have hC : ∀ {r τ a g}, .req (.inr ⟨.gc, .decide a g⟩) ∈ ρ.logic.input r τ →
      .ind (.decide a g) ∈ (ρ.child .gc).output r τ :=
    (Run.ind_mem_output_child (children_requestQuiet P Value t .gc)).2
  obtain h₁' : .req (.inr ⟨.gc, .decide (some v) true⟩) ∈ ρ.logic.input p τ := by
    rcases Logic.decide_gc_of_decide h₁ with h₁' | ⟨h, -⟩
    exacts [h₁', absurd h (by simp)]
  rcases Logic.decide_gc_of_decide h₂ with h₂' | ⟨-, ⟨g', h₂'⟩, -⟩
  · exact Option.some.inj
      (AttiyaWelch.consistency (hρ.child .gc) hn hp hq (hC h₁') (hC h₂'))
  · exact absurd (AttiyaWelch.consistency (hρ.child .gc) hn hp hq (hC h₁') (hC h₂'))
      (by simp)

/-! #### Latency -/

/-- **Latency** `δ + 9δ`: if every correct process has proposed by time `τ` and no correct process
abandons by `max τ gst + 10δ`, then every correct process decides by `max τ gst + 10δ`. Every
correct process has broadcast by `τ`, hence delivers, and proposes to AW′, by
`D = max τ gst + δ` (latency of the reducing broadcast), hence AW′ decides by `D + 9δ` (latency
of AW′), at a time at which the process has accepted its proposal. -/
theorem latency (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    (hprop : ∀ q ∉ ρ.faulty, ∃ v, ∃ τ' ≤ τ, .req (.inl (.propose v)) ∈ ρ.logic.input q τ')
    (hab : ∀ q ∉ ρ.faulty, ∀ τ' ≤ max τ ρ.gst + 10 * δ, .req (.inl .abandon) ∉ ρ.logic.input q τ')
    (hp : p ∉ ρ.faulty) :
    ∃ τ' ≤ max τ ρ.gst + 10 * δ, ∃ w g, .ind (.inl (.decide w g)) ∈ ρ.logic.output p τ' := by
  have hgst : (ρ.child .rb).gst = ρ.gst := rfl
  -- every correct process delivers by `max τ gst + δ`
  have hdel : ∀ q ∉ ρ.faulty,
      ∃ τ' ≤ max τ ρ.gst + δ, ∃ a, .ind (.deliver a) ∈ (ρ.child .rb).output q τ' := by
    intro q hq
    refine hgst ▸ ReducingBroadcast.latency (hρ.child .rb) (fun r hr => ?_)
      (fun r hr τ' hτ' h => hab r hr τ' (by rw [hgst] at hτ'; omega)
        (Logic.abandon_rb_iff.1 (Run.req_mem_input_child.1 h))) hq
    obtain ⟨v, τ', hτ', h⟩ := hprop r hr
    obtain ⟨τ'', hτ'', w, h'⟩ :=
      Logic.exists_broadcast_of_isSome_prop (Logic.isSome_prop_of_propose h)
    exact ⟨w, τ'', by omega, Run.req_mem_input_child.2 h'⟩
  -- hence proposes to AW′ by then
  have H : AttiyaWelch.Timely (ρ.child .gc) δ (max τ ρ.gst + δ) := by
    refine ⟨hρ.child .gc, hn, (le_max_right τ ρ.gst).trans (Nat.le_add_right _ _),
      fun q hq => ?_, fun q hq τ' hτ' h => hab q hq τ' (by omega)
        (Logic.abandon_gc_iff.1 (Run.req_mem_input_child.1 h))⟩
    obtain ⟨τ', hτ', a, h⟩ := hdel q hq
    exact ⟨a, τ', hτ', Run.req_mem_input_child.2 (Logic.propose_gc_of_deliver
      ((Run.ind_mem_output_child (children_requestQuiet P Value t .rb)).1 h)
      (isSome_prop_of_deliver hρ hq h))⟩
  obtain ⟨a, g, τ', hτ', h⟩ := H.decides hp
  obtain ⟨τ'', hτ'', w, g', h'⟩ := Logic.exists_decide_of_decide_gc
    ((Run.ind_mem_output_child (children_requestQuiet P Value t .gc)).1 h)
    (isSome_prop_of_decide_gc hρ hp h)
  exact ⟨τ'', by omega, w, g', h'⟩

end Composite

/-- **The reduced graded consensus is a graded consensus protocol** with latency `10δ = δ + 9δ`
for `3t < n`: strong validity (`strongValidity`), external validity (from
`exists_propose_of_decide` and the validity of correct proposals), consistency (`consistency`),
integrity (`atMostOnce`) and latency (`latency`). -/
theorem satisfies [Fintype P] [DecidableEq P] [DecidableEq Value] {t : ℕ}
    (hn : 3 * t < Fintype.card P) (valid : Value → Prop) (δ : ℕ) :
    (protocol P Value t).Satisfies t δ (GradedConsensus.spec valid (10 * δ)) := by
  intro ρ hρ hA
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hU p hp w g τ h
    exact strongValidity hρ hn (fun q hq w τ h => hU q hq w τ (Run.history_reqAt_compose.2 h)) hp
      (Run.history_indAt_compose.1 h)
  · intro p hp w g τ h
    obtain ⟨q, hq, τ', h'⟩ := exists_propose_of_decide hρ hn hp (Run.history_indAt_compose.1 h)
    exact hA.validProposal q hq w τ' (Run.history_reqAt_compose.2 h')
  · intro p q hp hq v w g τ τ' h₁ h₂
    exact consistency hρ hn hp hq (Run.history_indAt_compose.1 h₁) (Run.history_indAt_compose.1 h₂)
  · intro p _
    exact atMostOnce ρ p
  · intro τ hprop hab p hp
    obtain ⟨τ', hτ', w, g, h⟩ := latency hρ hn
      (fun q hq => let ⟨v, τ', hτ', h⟩ := hprop q hq; ⟨v, τ', hτ', Run.history_reqAt_compose.1 h⟩)
      (fun q hq τ' hτ' h => hab q hq ⟨τ', hτ', Run.history_reqAt_compose.2 h⟩) hp
    exact ⟨w, g, τ', hτ', Run.history_indAt_compose.2 h⟩

/-! ### Communication -/

section Communication

variable [Fintype P] [DecidableEq P] [DecidableEq Value] {t δ : ℕ} {ρ : Run (protocol P Value t)}
  {p : P}

variable (ρ) in
/-- The messages sent by a process are those of the two children (the logic sends none). -/
theorem bitsSent_one_eq_add (p : P) (a b : ℕ) :
    ρ.bitsSent (fun _ => 1) p a b =
      (ρ.child .rb).bitsSent (fun _ => 1) p a b + (ρ.child .gc).bitsSent (fun _ => 1) p a b := by
  have hsize : (fun _ => 1 : (protocol P Value t).Msg → ℕ) =
      Compose.msgSize (logic P Value) (children P Value t) (fun _ => 1) fun _ _ => 1 := by
    funext m
    rcases m with m | ⟨i, m⟩ <;> rfl
  rw [hsize, Run.bitsSent_compose_univ, Child.sum_univ,
    Run.bitsSent_eq_zero (ρ := ρ.logic) fun _ _ _ _ m => Empty.elim m, Nat.zero_add]

/-- **AW′ echoes at most five values in phase `1`** (in valid runs with `3t < n`, at correct
processes): AW′'s `⊥`, `some ⊥_rd`, and at most three values `some (some y)`. Each value `some y`
proposed to AW′ by a correct process was delivered by it, hence broadcast by `n - 3t` correct
processes (safety of the reducing broadcast), and every process broadcasts at most once
(`AttiyaWelch.card_sent_one_le_of_backed`). -/
theorem card_sent_one_le (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P) (hp : p ∉ ρ.faulty)
    (τ : ℕ) : #(((ρ.child .gc).state p τ).sent .one) ≤ 5 := by
  classical
  -- the correct broadcasters of each value
  let B : Option Value → Finset P := fun a => a.elim ∅ fun y =>
    univ.filter fun r => r ∉ ρ.faulty ∧ ∃ τ, .req (.broadcast y) ∈ (ρ.child .rb).input r τ
  refine (AttiyaWelch.card_sent_one_le_of_backed (hρ.child .gc) hn hp τ {none} (B := B) ?_ ?_).trans
    (by simp)
  · rintro (_ | x) hx (_ | y) hy hxy
    · simp at hx
    · simp at hx
    · simp at hy
    refine Finset.disjoint_left.2 fun r hrx hry => hxy ?_
    obtain ⟨-, τ₁, h₁⟩ := (Finset.mem_filter.1 hrx).2
    obtain ⟨-, τ₂, h₂⟩ := (Finset.mem_filter.1 hry).2
    rw [Logic.eq_of_broadcast (Run.req_mem_input_child.1 h₁) (Run.req_mem_input_child.1 h₂)]
  · rintro (_ | y) hy q hq τ' h
    · simp at hy
    obtain ⟨S, hS, hS'⟩ := ReducingBroadcast.safety (hρ.child .rb) hq (deliver_of_propose_gc h)
    refine hS.trans (card_le_card fun r hr => ?_)
    obtain ⟨hrF, τ'', -, h'⟩ := hS' r hr
    exact Finset.mem_filter.2 ⟨mem_univ r, hrF, τ'', h'⟩

/-- **Messages**: in a valid run with `3t < n`, in every window of time, a correct process sends
at most `11 n` messages: at most `n` of the reducing broadcast (`ReducingBroadcast.bitsSent_one_le`)
and at most `10 n` of AW′, since AW′ echoes at most five values in phase `1` (`card_sent_one_le`,
`AttiyaWelch.bitsSent_one_le_of_card_sent_one_le`); the logic sends nothing. -/
theorem bitsSent_one_le (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P) (hp : p ∉ ρ.faulty)
    (a b : ℕ) : ρ.bitsSent (fun _ => 1) p a b ≤ Fintype.card P * 11 := by
  rw [bitsSent_one_eq_add]
  have h₁ := ReducingBroadcast.bitsSent_one_le (ρ.child .rb) p a b
  have h₂ := AttiyaWelch.bitsSent_one_le_of_card_sent_one_le (ρ.child .gc) p a b
    (card_sent_one_le hρ hn hp b)
  calc _ ≤ Fintype.card P + Fintype.card P * (5 + 5) := Nat.add_le_add h₁ h₂
    _ = Fintype.card P * 11 := by omega

/-- The size of the encoding of `a : Option Value`, given the sizes `valueSize` of the encodings of
the values: one bit telling `⊥_rd` from a value, followed by the encoding of the value. -/
def optionSize (valueSize : Value → ℕ) : Option Value → ℕ
  | none => 1
  | some v => 1 + valueSize v

variable (P t) in
/-- The sizes of the messages of the children, given the sizes `valueSize` of the encodings of the
values: one bit telling the children apart, followed by the message of the child
(`ReducingBroadcast.Msg.size`, and `AttiyaWelch.Msg.size` for the sizes `optionSize valueSize`). -/
def childMsgSize (valueSize : Value → ℕ) : (i : Child) → (children P Value t i).Msg → ℕ
  | .rb => fun m => 1 + ReducingBroadcast.Msg.size valueSize m
  | .gc => fun m => 1 + AttiyaWelch.Msg.size (optionSize valueSize) m

variable (P t) in
/-- The sizes of the messages of the reduced graded consensus (`Compose.msgSize`; the logic sends
no messages). -/
noncomputable def msgSize (valueSize : Value → ℕ) : (protocol P Value t).Msg → ℕ :=
  Compose.msgSize _ _ Empty.elim (childMsgSize P t valueSize)

/-- A message has at most `L + 7` bits if every value has at most `L` bits. -/
theorem msgSize_le {valueSize : Value → ℕ} {L : ℕ} (hL : ∀ v, valueSize v ≤ L)
    (m : (protocol P Value t).Msg) : msgSize P t valueSize m ≤ L + 7 := by
  rcases m with ⟨⟨⟩⟩ | ⟨_ | _, m⟩
  · have := ReducingBroadcast.Msg.size_le hL m
    change 1 + ReducingBroadcast.Msg.size valueSize m ≤ L + 7
    omega
  · have := AttiyaWelch.Msg.size_le (valueSize := optionSize valueSize) (L := L + 1)
      (fun a => by cases a with
        | none => simp [optionSize]
        | some v => have := hL v; simp only [optionSize]; omega) m
    change 1 + AttiyaWelch.Msg.size (optionSize valueSize) m ≤ L + 7
    omega

/-- **Bits**: in a valid run with `3t < n`, in every window of time, a correct process sends at most
`11 n (L + 7)` bits if every value is encoded with at most `L` bits (`msgSize`), i.e. `O(n L)` bits
for every `t < n / 3`. -/
theorem bitsSent_le (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P) (hp : p ∉ ρ.faulty)
    (a b : ℕ) {valueSize : Value → ℕ} {L : ℕ} (hL : ∀ v, valueSize v ≤ L) :
    ρ.bitsSent (msgSize P t valueSize) p a b ≤ Fintype.card P * 11 * (L + 7) :=
  (Run.bitsSent_le_mul (msgSize_le hL)).trans
    (Nat.mul_le_mul_right _ (bitsSent_one_le hρ hn hp a b))

/-! #### Raw bounds (every run, any number of faulty processes)

The bounds above use the validity of the run (at most `t` faulty processes) through the safety of
the reducing broadcast. The following ones hold in every run, whatever the number of faulty
processes; they depend on `n / (t + 1)`, which is at most `3` for the largest admissible threshold
(`n ≤ 3 (t + 1)`). -/

/-- **Messages in every run**: in every window of time, a process sends at most
`n (n / (t + 1) + 7)` messages: at most `n` of the reducing broadcast
(`ReducingBroadcast.bitsSent_one_le`) and at most `n (n / (t + 1) + 6)` of AW′
(`AttiyaWelch.bitsSent_one_le`). No validity of the run is needed. -/
theorem bitsSent_one_le_div (ρ : Run (protocol P Value t)) (p : P) (a b : ℕ) :
    ρ.bitsSent (fun _ => 1) p a b ≤ Fintype.card P * (Fintype.card P / (t + 1) + 7) := by
  rw [bitsSent_one_eq_add]
  calc _ ≤ Fintype.card P + Fintype.card P * (Fintype.card P / (t + 1) + 6) :=
        Nat.add_le_add (ReducingBroadcast.bitsSent_one_le (ρ.child .rb) p a b)
          (AttiyaWelch.bitsSent_one_le (ρ.child .gc) p a b)
    _ = Fintype.card P * (Fintype.card P / (t + 1) + 7) := by
        rw [Nat.mul_add, Nat.mul_add]; omega

/-- **Bits in every run**: in every window of time, a process sends at most
`n (n / (t + 1) + 7) (L + 7)` bits if every value is encoded with at most `L` bits (`msgSize`).
No validity of the run is needed. -/
theorem bitsSent_le_div (ρ : Run (protocol P Value t)) (p : P) (a b : ℕ)
    {valueSize : Value → ℕ} {L : ℕ} (hL : ∀ v, valueSize v ≤ L) :
    ρ.bitsSent (msgSize P t valueSize) p a b ≤
      Fintype.card P * (Fintype.card P / (t + 1) + 7) * (L + 7) :=
  (Run.bitsSent_le_mul (msgSize_le hL)).trans
    (Nat.mul_le_mul_right _ (bitsSent_one_le_div ρ p a b))

/-- **Messages in every run, for the largest threshold**: if `n ≤ 3 (t + 1)` (e.g.
`t = ⌊(n - 1) / 3⌋`), a process sends at most `10 n` messages in every window of time
(`bitsSent_one_le_div`, `n / (t + 1) ≤ 3`). No validity of the run is needed. -/
theorem bitsSent_one_le_of_card_le (ht : Fintype.card P ≤ 3 * (t + 1))
    (ρ : Run (protocol P Value t)) (p : P) (a b : ℕ) :
    ρ.bitsSent (fun _ => 1) p a b ≤ Fintype.card P * 10 :=
  (bitsSent_one_le_div ρ p a b).trans (Nat.mul_le_mul_left _ (by
    have := Nat.div_le_of_le_mul (m := Fintype.card P) (k := t + 1) (n := 3) (by omega); omega))

/-- **Bits in every run, for the largest threshold**: if `n ≤ 3 (t + 1)`, a process sends at most
`10 n (L + 7)` bits in every window of time if every value is encoded with at most `L` bits
(`msgSize`). No validity of the run is needed. -/
theorem bitsSent_le_of_card_le (ht : Fintype.card P ≤ 3 * (t + 1))
    (ρ : Run (protocol P Value t)) (p : P) (a b : ℕ) {valueSize : Value → ℕ} {L : ℕ}
    (hL : ∀ v, valueSize v ≤ L) :
    ρ.bitsSent (msgSize P t valueSize) p a b ≤ Fintype.card P * 10 * (L + 7) :=
  (Run.bitsSent_le_mul (msgSize_le hL)).trans
    (Nat.mul_le_mul_right _ (bitsSent_one_le_of_card_le ht ρ p a b))

end Communication

end Cslib.Distributed.ReducedGradedConsensus
