/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Consensus

/-!
# Sanity check: the model's liveness semantics are not degenerate

A tiny algorithm that solves consensus (with *correct-proposal validity*) when there are no
faults (`t = 0`), for every `δ` and every GST: every process keeps broadcasting its proposal and
decides the first value it receives from a fixed leader `p₀`. This checks that messages between
correct processes are indeed delivered (`Run.Valid`) and processed (`Run.st_succ`), so that
`SolvesConsensus` is satisfiable in the model and the impossibility results are not vacuous for
trivial reasons.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync.Examples

variable {P V : Type*} [Fintype P] [DecidableEq P]

/-- Everybody broadcasts its proposal forever; decide the first value heard from `p₀`. -/
def leaderEcho (p₀ : P) : Algorithm P V (V × Option V) V V where
  init p v := (v, if p = p₀ then some v else none)
  step _ s ib := (s.1, s.2.or (ib p₀).head?)
  send _ s _ := [s.1]
  decide _ s := s.2

/-- Correct-proposal validity: the decision is the proposal of some correct process. -/
def correctProposal : ValidityProperty P V V := fun c => {v | ∃ p, c p = some v}

variable {p₀ : P} {R : Run P V V}

omit [Fintype P] in
theorem st_succ' (τ : ℕ) (p : P) : R.st (leaderEcho p₀) (τ + 1) p =
    ((R.st (leaderEcho p₀) τ p).1,
      (R.st (leaderEcho p₀) τ p).2.or (R.inbox (leaderEcho p₀) p τ p₀).head?) :=
  R.st_succ _ τ p

omit [Fintype P] in
theorem fst_st (τ : ℕ) (p : P) : (R.st (leaderEcho p₀) τ p).1 = R.inp p := by
  induction τ with
  | zero => simp [leaderEcho]
  | succ τ ih => rw [st_succ']; exact ih

omit [Fintype P] in
theorem snd_st (hp₀ : p₀ ∉ R.faulty) (τ : ℕ) (p : P) :
    (R.st (leaderEcho p₀) τ p).2 = none ∨ (R.st (leaderEcho p₀) τ p).2 = some (R.inp p₀) := by
  induction τ with
  | zero => by_cases hp : p = p₀ <;> simp [leaderEcho, hp]
  | succ τ ih =>
    rw [st_succ']
    rcases ih with h | h
    · rw [h, Option.none_or]
      -- every message from `p₀` carries its proposal
      have hall : ∀ m ∈ R.inbox (leaderEcho p₀) p τ p₀, m = R.inp p₀ := by
        intro m hm
        rw [Run.inbox_eq_flatMap, List.mem_flatMap] at hm
        obtain ⟨σ, -, hm⟩ := hm
        simp only [Run.dlv] at hm
        split_ifs at hm
        · rw [Run.out_of_correct _ _ hp₀] at hm
          rw [List.mem_singleton.mp hm, fst_st]
        · simp at hm
      cases hl : R.inbox (leaderEcho p₀) p τ p₀ with
      | nil => simp
      | cons m l => simp [hall m (by simp [hl])]
    · rw [h]; simp

omit [Fintype P] in
/-- With no faults, `leaderEcho` solves consensus with correct-proposal validity. -/
theorem leaderEcho_solves (δ : ℕ) :
    SolvesConsensus 0 δ (leaderEcho (V := V) p₀) correctProposal where
  termination R hR p hp := by
    have hF : R.faulty = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hR.card_faulty)
    have hp₀ : p₀ ∉ R.faulty := by simp [hF]
    refine ⟨R.inp p₀, ?_⟩
    -- the batch sent by `p₀` at time `0` is delivered at time `D`
    set D := R.dl p₀ 0 p
    rcases snd_st hp₀ D p with h | h
    · refine ⟨D + 1, ?_⟩
      have hmem : R.inp p₀ ∈ R.inbox (leaderEcho p₀) p D p₀ := by
        rw [Run.inbox_eq_flatMap, List.mem_flatMap]
        refine ⟨0, by simp, ?_⟩
        simp [Run.dlv, D, Run.out_of_correct _ _ hp₀, leaderEcho]
      rcases snd_st hp₀ (D + 1) p with h' | h'
      · exfalso
        rw [st_succ', h, Option.none_or, List.head?_eq_none_iff] at h'
        simp [h'] at hmem
      · exact h'
    · exact ⟨D, h⟩
  agreement R hR p _ q _ v w hv hw := by
    have hF : R.faulty = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hR.card_faulty)
    have hp₀ : p₀ ∉ R.faulty := by simp [hF]
    obtain ⟨τ, hτ⟩ := hv
    obtain ⟨τ', hτ'⟩ := hw
    rcases snd_st hp₀ τ p with h | h <;> rcases snd_st hp₀ τ' q with h' | h' <;>
      simp_all [leaderEcho]
  validity R hR p _ v hv := by
    have hF : R.faulty = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hR.card_faulty)
    have hp₀ : p₀ ∉ R.faulty := by simp [hF]
    obtain ⟨τ, hτ⟩ := hv
    refine ⟨p₀, ?_⟩
    rcases snd_st hp₀ τ p with h | h <;> simp_all [leaderEcho, Run.inputConf]

end Cslib.Byzantine.PartialSync.Examples
