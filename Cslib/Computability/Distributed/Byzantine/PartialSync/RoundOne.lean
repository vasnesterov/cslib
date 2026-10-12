/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Auth

/-!
# Executions that are synchronous in their first two rounds ("good-case" executions)

Generic infrastructure for *good-case latency* lower bounds in the partially synchronous model (as
in Section 4 of Kuznetsov, Tonkikh and Zhang [KuznetsovTonkikhZhang2021]). Rounds have length `D`
(`= δ`); round `i` is `[(i-1)D, iD)`.

* `quiet A p v τ`: the state of `p` (input `v`) after `τ` steps without receiving anything.
* `nextRound D τ`: the first multiple of `D` strictly after `τ` ("beginning of the next round").
* `round1 A q ov τ x`: the round-1 messages of `q` towards `x` if `q` runs the algorithm with input
  `v` (`ov = some v`) or is silent (`none`).
* `templateRun A D F I G r1 later dl`: a run whose Byzantine processes `F` behave in round 1 like
  correct processes with a chosen input per receiver (`r1 q x`), and arbitrarily afterwards
  (`later`); delivery times `dl`.
* `RoundSched D dl`: round-1 batches are delivered at time `D`, later batches not before `2D`.
  Then (`templateRun_st_early`, `templateRun_out_early`, `templateRun_inbox_early`,
  `templateRun_st_eq_early`): up to time `2D` a process's state only depends on its input and on
  the round-1 inputs of the others towards it ("Lemma 4.1" of KTZ21).
* Signatures: `quiet_tokens`, `round1_tokens` — a process that received nothing only emits its own
  tokens (via `silentRun`, the run in which everybody is Byzantine and silent).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S V W K : Type*} [Fintype P] [DecidableEq P]

/-- The state of `p` with input `v` after `τ` steps in which it receives nothing. -/
def quiet (A : Algorithm P M S V W) (p : P) (v : V) : ℕ → S
  | 0 => A.init p v
  | τ + 1 => A.step p (quiet A p v τ) fun _ => []

/-- The first multiple of `D` strictly greater than `τ` (for `0 < D`). -/
def nextRound (D τ : ℕ) : ℕ := τ - τ % D + D

section nextRound

variable {D τ : ℕ}

theorem nextRound_of_lt (h : τ < D) : nextRound D τ = D := by
  simp [nextRound, Nat.mod_eq_of_lt h]

theorem nextRound_of_lt_two (h1 : D ≤ τ) (h2 : τ < 2 * D) : nextRound D τ = 2 * D := by
  have : τ % D = τ - D := by rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  simp only [nextRound, this]; omega

theorem two_le_nextRound (h1 : D ≤ τ) : 2 * D ≤ nextRound D τ := by
  have : τ % D ≤ τ - D := by rw [Nat.mod_eq_sub_mod h1]; exact Nat.mod_le _ _
  simp only [nextRound]; omega

theorem three_le_nextRound (h1 : 2 * D ≤ τ) : 3 * D ≤ nextRound D τ := by
  have : τ % D ≤ τ - 2 * D := by
    rw [Nat.mod_eq_sub_mod (by omega : D ≤ τ), Nat.mod_eq_sub_mod (by omega : D ≤ τ - D)]
    exact (Nat.mod_le _ _).trans (by omega)
  simp only [nextRound]; omega

theorem le_nextRound (hD : 0 < D) : τ < nextRound D τ := by
  have := Nat.mod_lt τ hD
  have := Nat.mod_le τ D
  simp only [nextRound]; omega

theorem nextRound_le : nextRound D τ ≤ τ + D := by
  have := Nat.mod_le τ D
  simp only [nextRound]; omega

end nextRound

variable (A : Algorithm P M S V W)

/-- Round-1 messages of `q` to `x` at time `τ` when `q` runs the protocol with input `v`
(`some v`), or nothing (`none`). -/
def round1 (q : P) (ov : Option V) (τ : ℕ) (x : P) : List M :=
  match ov with
  | none => []
  | some v => A.send q (quiet A q v τ) x

/-- Template for the executions of the lower bound. `F`: Byzantine processes; `I`: inputs;
`G`: GST; `r1 q x`: the input with which the Byzantine `q` runs the protocol towards `x` during
the first round (`none`: silent); `later q τ x`: what the Byzantine `q` sends from time `D` on;
`dl`: delivery times. -/
def templateRun (D : ℕ) (F : Finset P) (I : P → V) (G : ℕ) (r1 : P → P → Option V)
    (later : P → ℕ → P → List M) (dl : P → ℕ → P → ℕ) : Run P M V where
  faulty := F
  inp := I
  gst := G
  byz q τ x := if τ < D then round1 A q (r1 q x) τ x else later q τ x
  dl := dl


/-- The "effective" round-1 input of `q` towards `x` in `templateRun`. -/
def templateEff (F : Finset P) (I : P → V) (r1 : P → P → Option V) (q x : P) : Option V :=
  if q ∈ F then r1 q x else some (I q)

/-- The schedule requirement of `templateRun`: round-1 messages are delivered at `D`, and nothing
sent later is delivered before `2D`. -/
def RoundSched (D : ℕ) (dl : P → ℕ → P → ℕ) : Prop :=
  ∀ q τ x, (τ < D → dl q τ x = D) ∧ (D ≤ τ → 2 * D ≤ dl q τ x)

omit [DecidableEq P] [Fintype P] in
theorem roundSched_nextRound {D : ℕ} : RoundSched (P := P) D (fun _ τ _ => nextRound D τ) :=
  fun _ _ _ => ⟨nextRound_of_lt, two_le_nextRound⟩


section early

variable {A} {D : ℕ} {F : Finset P} {I : P → V} {G : ℕ} {r1 : P → P → Option V}
  {later : P → ℕ → P → List M} {dl : P → ℕ → P → ℕ}

omit [Fintype P] in
/-- **Lemma 4.1.** During the first round, the state of every process depends only on its input. -/
theorem templateRun_st_early (hS : RoundSched D dl) (x : P) :
    ∀ τ ≤ D, (templateRun A D F I G r1 later dl).st A τ x = quiet A x (I x) τ := by
  intro τ hτ
  induction τ with
  | zero => rfl
  | succ τ ih =>
    rw [Run.st_succ, ih (by omega)]
    change _ = A.step x (quiet A x (I x) τ) fun _ => []
    congr 1
    funext q
    rw [Run.inbox_eq_flatMap]
    apply List.flatMap_eq_nil_iff.mpr
    intro τ' hτ'
    simp only [List.mem_range] at hτ'
    exact Run.dlv_eq_nil_of_ne _ _ (by
      change dl q τ' x ≠ τ
      rw [(hS q τ' x).1 (by omega)]; omega)

omit [Fintype P] in
theorem templateRun_out_early (hS : RoundSched D dl) {τ : ℕ} (hτ : τ < D) (q x : P) :
    (templateRun A D F I G r1 later dl).out A q τ x = round1 A q (templateEff F I r1 q x) τ x := by
  by_cases hq : q ∈ F
  · rw [Run.out_of_faulty _ _ hq]
    simp [templateRun, templateEff, hq, hτ]
  · rw [Run.out_of_correct _ _ hq, templateRun_st_early hS q τ hτ.le]
    simp [templateEff, hq, round1]

omit [Fintype P] in
/-- Inbox of `x` before time `2D`: only the round-1 messages, delivered at time `D`. -/
theorem templateRun_inbox_early (hS : RoundSched D dl) {τ : ℕ} (hτ : τ < 2 * D) (x : P) :
    (templateRun A D F I G r1 later dl).inbox A x τ = fun q => (List.range (τ + 1)).flatMap
      fun τ' => if τ' < D ∧ τ = D then round1 A q (templateEff F I r1 q x) τ' x else [] := by
  funext q
  rw [Run.inbox_eq_flatMap]
  refine List.flatMap_congr fun τ' _ => ?_
  simp only [Run.dlv]
  by_cases h1 : τ' < D
  · change (if dl q τ' x = τ then _ else _) = _
    rw [(hS q τ' x).1 h1, templateRun_out_early hS h1]
    by_cases h2 : τ = D
    · simp [h1, h2]
    · simp [h1, h2, Ne.symm h2]
  · have := (hS q τ' x).2 (by omega)
    have h3 : (templateRun A D F I G r1 later dl).dl q τ' x ≠ τ := by
      change dl q τ' x ≠ τ; omega
    simp [h1, h3]

omit [Fintype P] in
/-- Two template executions in which `x` has the same input and the same round-1 view are
indistinguishable for `x` up to time `2D`. -/
theorem templateRun_st_eq_early {F' : Finset P} {I' : P → V} {G' : ℕ} {r1' : P → P → Option V}
    {later' : P → ℕ → P → List M} {dl' : P → ℕ → P → ℕ} (hS : RoundSched D dl)
    (hS' : RoundSched D dl')
    {x : P} (hI : I x = I' x) (heff : ∀ q, templateEff F I r1 q x = templateEff F' I' r1' q x) :
    ∀ τ ≤ 2 * D, (templateRun A D F I G r1 later dl).st A τ x =
      (templateRun A D F' I' G' r1' later' dl').st A τ x := by
  intro τ hτ
  refine (templateRun A D F I G r1 later dl).st_eq_of_inbox_eq A
    (ref := fun _ => templateRun A D F' I' G' r1' later' dl') (X := {x}) (T := 2 * D) ?_ ?_ τ hτ x
    rfl
  · rintro p rfl; exact hI
  · rintro τ hτ _ p rfl
    rw [templateRun_inbox_early hS hτ, templateRun_inbox_early hS' hτ]
    simp only [heff]

end early

/-! ### Signatures -/

/-- The run in which every process is Byzantine and silent: every process receives nothing. -/
def silentRun (v : V) : Run P M V where
  faulty := univ
  inp _ := v
  gst := 0
  byz _ _ _ := []
  dl _ τ _ := τ

theorem silentRun_out (v : V) (q : P) (τ : ℕ) (x : P) : (silentRun (M := M) v).out A q τ x = [] :=
  Run.out_of_faulty A (silentRun v) (show q ∈ (silentRun (M := M) v).faulty from mem_univ q) τ x

theorem silentRun_st (v : V) (q : P) : ∀ τ, (silentRun (M := M) v).st A τ q = quiet A q v τ := by
  intro τ
  induction τ with
  | zero => rfl
  | succ τ ih =>
    rw [Run.st_succ, ih]
    change _ = A.step q (quiet A q v τ) fun _ => []
    congr 1
    funext r
    rw [Run.inbox_eq_flatMap]
    apply List.flatMap_eq_nil_iff.mpr
    intro τ' _
    simp [Run.dlv, silentRun_out]

set_option linter.unusedFintypeInType false in
/-- A process that has received nothing only emits its own signatures. -/
theorem quiet_tokens {Au : Auth P M K} (hU : A.Unforging Au) {q : P} {v : V} {τ : ℕ} {x : P}
    {m : M} (hm : m ∈ A.send q (quiet A q v τ) x) {k : K} (hk : k ∈ Au.tokens m) :
    Au.signer k = q := by
  rw [← silentRun_st (M := M) A v q τ] at hm
  rcases hU _ q τ x m hm k hk with h | ⟨τ', _, r, m', hm', _⟩
  · exact h
  · obtain ⟨σ, -, -, hm''⟩ := Run.mem_inbox.mp hm'
    simp [silentRun_out] at hm''

set_option linter.unusedFintypeInType false in
theorem round1_tokens {Au : Auth P M K} (hU : A.Unforging Au) {q : P} {ov : Option V} {τ : ℕ}
    {x : P} {m : M} (hm : m ∈ round1 A q ov τ x) {k : K} (hk : k ∈ Au.tokens m) :
    Au.signer k = q := by
  cases ov with
  | none => simp [round1] at hm
  | some v => exact quiet_tokens A hU hm hk

/-! ### The two-step execution is an admissible execution -/


end Cslib.Byzantine.PartialSync
