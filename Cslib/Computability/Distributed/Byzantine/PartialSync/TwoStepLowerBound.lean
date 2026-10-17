/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.RoundOne
public import Cslib.Computability.Distributed.Byzantine.PartialSync.QuietRuns

/-!
# Two-step executions and the executions `ρ₁, …, ρ₅` of the two-step lower bound

Kuznetsov–Tonkikh–Zhang, *Revisiting optimal resilience of fast Byzantine consensus*, PODC 2021,
Sections 4.1–4.2 (Figures 2–4); the same executions prove the good-case latency lower bound of
Abraham–Nayak–Ren–Xiang, PODC 2021, Theorem 7 (Figure 4).

* `tsRun A D I T`: the **`T`-faulty two-step execution** starting from `I`, with rounds of length
  `D`: the processes of `T` are Byzantine, follow the protocol during the first round and are
  silent afterwards; every message sent in a round is delivered at the beginning of the next round
  (`nextRound`), `gst = 0`.

The processes are labelled by `g : P → ℕ`: label `0` is a single process `p`, labels `1, …, 5` are
the groups `P₁, …, P₅`. `ρ₅ = tsRun (I[p ↦ a]) P₅` is a two-step execution, and `ρ₃`
(`TwoStepLB.rho3`, Byzantine: `{p} ∪ P₃`) is the synchronous execution in which `p` sends its `ρ₅`
round-1 messages to `P₁ ∪ P₂` and its round-1 messages for `b` to `P₄ ∪ P₅`, and `P₃` crashes after
round 1. `TwoStepLB.rho4` (Byzantine: `{p} ∪ P₄`; `P₃` correct but slow; `P₅`'s round-2+ messages
to `P₃` late) satisfies

* `ρ₄ ∼_{P₃} ρ₅` up to time `2D + 1` (`TwoStepLB.rho4_st_eq_rho5_P3`),
* `ρ₄ ∼_{P₁ ∪ P₂ ∪ P₅} ρ₃` up to the decision time `T` of a process in `ρ₃`
  (`TwoStepLB.rho4_st_eq_rho3`),
* `ρ₄` is admissible: at most `|{p} ∪ P₄|` faults, partial synchrony with `gst = T + 2D + 1`,
  unforgeability (`TwoStepLB.rho4_valid`, `TwoStepLB.rho4_authValid`),

so agreement in `ρ₄` forces the decision of `P₁ ∪ P₂ ∪ P₅` in `ρ₃` to be the decision of `P₃` in
`ρ₅` within two rounds (`TwoStepLB.decision_eq`). The mirror image (labels `i ↦ 6 - i`, `a ↔ b`)
needs no separate construction.
-/

@[expose] public section

set_option linter.unusedSectionVars false


namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S V K : Type*} [Fintype P] [DecidableEq P]

section tsRun

variable (A : Algorithm P M S V V)

/-- The **`T`-faulty two-step execution** starting from `I` (Section 4.1), with rounds of length
`D` (= `δ`): the processes in `T` are Byzantine, follow the protocol during the first round and
then stop; every message sent in a round is delivered at the beginning of the next round. -/
def tsRun (D : ℕ) (I : P → V) (T : Finset P) : Run P M V where
  faulty := T
  inp := I
  gst := 0
  byz q τ x := if τ < D then A.send q (quiet A q (I q) τ) x else []
  dl _ τ _ := nextRound D τ

omit [Fintype P] [DecidableEq P] in
/-- A two-step execution is a template execution (CSLib `RoundOne`). -/
theorem tsRun_eq (D : ℕ) (I : P → V) (T : Finset P) :
    tsRun (M := M) A D I T = templateRun A D T I 0 (fun q _ => some (I q)) (fun _ _ _ => [])
      (fun _ τ _ => nextRound D τ) := rfl

omit [Fintype P] [DecidableEq P] in
/-- A two-step execution is admissible (synchronous) when `|T| ≤ f`. -/
theorem tsRun_valid {f δ : ℕ} (hδ : 0 < δ) (I : P → V) {T : Finset P} (hT : T.card ≤ f) :
    (tsRun (M := M) A δ I T).Valid f δ where
  card_faulty := hT
  dl_ge _ _ _ _ _ := (le_nextRound hδ).le
  dl_le _ _ _ _ _ := nextRound_le.trans (by simp [tsRun])

set_option linter.unusedFintypeInType false in
/-- A two-step execution respects unforgeability: Byzantine processes only send their own
round-1 messages. -/
theorem tsRun_authValid {Au : Auth P M K} (hU : A.Unforging Au) (D : ℕ) (I : P → V)
    (T : Finset P) : (tsRun (M := M) A D I T).AuthValid Au A := by
  intro b hb τ r _ m hm k hk
  simp only [tsRun] at hm
  split_ifs at hm
  · left; rw [quiet_tokens A hU hm hk]; exact hb
  · simp at hm
end tsRun

namespace TwoStepLB

section rho4

variable (A : Algorithm P M S V V) (D : ℕ) (g : P → ℕ) (p : P) (I : P → V) (a b : V)
  (T5 : Finset P) (ρ3 : Run P M V) (T : ℕ)

/-- The Byzantine processes of `ρ₄`: `{p} ∪ P₄`. -/
def F4 : Finset P := univ.filter fun q => g q = 0 ∨ g q = 4

/-- Execution `ρ₄` (Figure 3b). `T`: the time by which the chosen process of `P₁` has decided in
`ρ₃`. -/
def rho4 : Run P M V :=
  templateRun A D (F4 g) I (T + 2 * D + 1)
    (fun q x => if q = p then (if g x = 5 then some b else some a) else some (I q))
    (fun q τ x =>
      if q = p then
        (if g x = 3 ∧ τ < 2 * D then (tsRun A D (Function.update I p a) T5).out A p τ x else [])
      else if g x = 3 then
        (if τ < 2 * D then (tsRun A D (Function.update I p a) T5).out A q τ x else [])
      else (if τ ≤ T then ρ3.out A q τ x else []))
    (fun q τ x => if D ≤ τ ∧ ((g q = 3 ∧ g x ≠ 3) ∨ (g q = 5 ∧ g x = 3)) then
      max (nextRound D τ) (T + 2 * D + 1) else nextRound D τ)

variable {A D g p I a b T5 ρ3 T}

omit [DecidableEq P] in
/-- Membership in the Byzantine set of `ρ₄`. -/
theorem mem_F4 {q : P} : q ∈ F4 g ↔ g q = 0 ∨ g q = 4 := by simp [F4]

omit [Fintype P] [DecidableEq P] in
/-- The delivery schedule of `ρ₄` is a round schedule (round-1 messages arrive at `D`). -/
theorem sched_rho4 :
    RoundSched D (fun q τ x => if D ≤ τ ∧ ((g q = 3 ∧ g x ≠ 3) ∨ (g q = 5 ∧ g x = 3)) then
      max (nextRound D τ) (T + 2 * D + 1) else nextRound D τ) := by
  intro q τ x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [show ¬ D ≤ τ by omega, false_and, ite_false]; exact nextRound_of_lt h
  · have := two_le_nextRound (D := D) h
    beta_reduce
    split_ifs <;> omega

end rho4

section side

variable {A : Algorithm P M S V V} {Au : Auth P M K} {f D : ℕ} {g : P → ℕ} {p : P}
  {I : P → V} {a b : V} {T5 F3 : Finset P} {J : P → V} {r3 : P → P → Option V}

/-- The common hypotheses of the side lemma. -/
structure SideHyp (g : P → ℕ) (p : P) (I : P → V) (a b : V) (T5 F3 : Finset P) (J : P → V)
    (r3 : P → P → Option V) : Prop where
  hp : ∀ q, g q = 0 ↔ q = p
  hg : ∀ q, g q ≤ 5
  hT5 : ∀ q, q ∈ T5 ↔ g q = 5
  hF3 : ∀ q, q ∈ F3 ↔ g q = 0 ∨ g q = 3
  hJ : ∀ q, q ≠ p → J q = I q
  hr3a : ∀ x, g x = 1 ∨ g x = 2 → r3 p x = some a
  hr3b : ∀ x, g x = 4 ∨ g x = 5 → r3 p x = some b
  hr3 : ∀ q, g q = 3 → ∀ x, r3 q x = some (I q)

/-- `ρ₃` as a template execution. -/
abbrev rho3 (A : Algorithm P M S V V) (D : ℕ) (F3 : Finset P) (J : P → V)
    (r3 : P → P → Option V) : Run P M V :=
  templateRun A D F3 J 0 r3 (fun _ _ _ => []) (fun _ τ _ => nextRound D τ)

variable (h : SideHyp g p I a b T5 F3 J r3)
include h

omit [Fintype P] [DecidableEq P] in
/-- Only the process `p` has label `0`. -/
theorem SideHyp.ne_p {q : P} (hq : g q ≠ 0) : q ≠ p := fun e => hq ((h.hp q).mpr e)

omit [Fintype P] [DecidableEq P] in
/-- The process `p` has label `0`. -/
theorem SideHyp.gp : g p = 0 := (h.hp p).mpr rfl

/-- `ρ₄ ∼ ρ₅` for `P₁ ∪ P₂ ∪ P₃` up to time `2D` (round-1 views coincide). -/
theorem rho4_st_eq_rho5 (T : ℕ) {y : P} (hy : g y = 1 ∨ g y = 2 ∨ g y = 3) :
    ∀ τ ≤ 2 * D, (rho4 A D g p I a b T5 (rho3 A D F3 J r3) T).st A τ y =
      (tsRun A D (Function.update I p a) T5).st A τ y := by
  have hyp : y ≠ p := h.ne_p (by omega)
  rw [tsRun_eq]
  refine templateRun_st_eq_early sched_rho4 roundSched_nextRound (by simp [hyp]) fun q => ?_
  by_cases hq : q = p
  · subst hq
    have h1 : q ∈ F4 g := mem_F4.mpr (Or.inl h.gp)
    have h2 : q ∉ T5 := fun hm => by have := (h.hT5 q).mp hm; rw [h.gp] at this; omega
    simp [templateEff, h1, h2, show g y ≠ 5 by omega]
  · by_cases h1 : q ∈ F4 g <;> by_cases h2 : q ∈ T5 <;> simp [templateEff, h1, h2, hq]

/-- `ρ₄ ∼_{P₃} ρ₅` up to time `2D + 1`: `P₃` receives in round 2 exactly what it receives in
`ρ₅` (from `p` and `P₄` by replay, from `P₁ ∪ P₂ ∪ P₃` since they are in the same state, nothing
from `P₅`). -/
theorem rho4_st_eq_rho5_P3 (hD : 0 < D) (T : ℕ) {y : P} (hy : g y = 3) :
    ∀ τ ≤ 2 * D + 1, (rho4 A D g p I a b T5 (rho3 A D F3 J r3) T).st A τ y =
      (tsRun A D (Function.update I p a) T5).st A τ y := by
  intro τ hτ
  rcases Nat.lt_or_ge τ (2 * D + 1) with hτ' | hτ'
  · exact rho4_st_eq_rho5 h T (by omega) τ (by omega)
  obtain rfl : τ = 2 * D + 1 := by omega
  rw [Run.st_succ, Run.st_succ, rho4_st_eq_rho5 h T (by omega) _ le_rfl]
  congr 1
  apply Run.inbox_eq_of_dlv_eq
  intro q τ' hτ'
  simp only [Run.dlv]
  set R4 := rho4 A D g p I a b T5 (rho3 A D F3 J r3) T
  set R5 := tsRun (M := M) A D (Function.update I p a) T5
  have hd5 : R5.dl q τ' y = nextRound D τ' := rfl
  have hd4 : R4.dl q τ' y = if D ≤ τ' ∧ ((g q = 3 ∧ g y ≠ 3) ∨ (g q = 5 ∧ g y = 3)) then
      max (nextRound D τ') (T + 2 * D + 1) else nextRound D τ' := rfl
  have hd4' : D ≤ τ' → ¬ (g q = 3 ∧ g y ≠ 3) := fun _ h' => h'.2 hy
  by_cases h1 : τ' < D
  · have e5 : R5.dl q τ' y ≠ 2 * D := by rw [hd5, nextRound_of_lt h1]; omega
    have e4 : R4.dl q τ' y ≠ 2 * D := by
      rw [hd4, ite_eq_right (by omega), nextRound_of_lt h1]; omega
    simp [e4, e5]
  by_cases h2 : τ' = 2 * D
  · have := three_le_nextRound (D := D) (τ := τ') (by omega)
    have e5 : R5.dl q τ' y ≠ 2 * D := by rw [hd5]; omega
    have e4 : R4.dl q τ' y ≠ 2 * D := by
      rw [hd4]; split_ifs
      · have := le_max_left (nextRound D τ') (T + 2 * D + 1); omega
      · omega
    simp [e4, e5]
  have h3 := nextRound_of_lt_two (D := D) (τ := τ') (by omega) (by omega)
  by_cases hq5 : g q = 5
  · have hq : q ∈ R5.faulty := (h.hT5 q).mpr hq5
    have : R5.out A q τ' y = [] := by
      rw [Run.out_of_faulty A R5 hq]; simp [R5, tsRun, h1]
    have e4 : R4.dl q τ' y ≠ 2 * D := by
      rw [hd4, ite_eq_left ⟨by omega, Or.inr ⟨hq5, hy⟩⟩]
      have := le_max_right (nextRound D τ') (T + 2 * D + 1); omega
    simp [e4, this]
  have e4 : R4.dl q τ' y = 2 * D := by
    rw [hd4, ite_eq_right (by omega), h3]
  rw [e4, hd5, h3]
  simp only [ite_true]
  by_cases hqp : q = p
  · subst hqp
    rw [Run.out_of_faulty A R4 (mem_F4.mpr (Or.inl h.gp))]
    simp [R4, rho4, templateRun, h1, hy, show τ' < 2 * D by omega]
    rfl
  by_cases hq4 : g q = 4
  · rw [Run.out_of_faulty A R4 (mem_F4.mpr (Or.inr hq4))]
    simp [R4, rho4, templateRun, h1, hy, hqp, show τ' < 2 * D by omega]
    rfl
  have hq4' : q ∉ R4.faulty := fun hm => by
    rcases mem_F4.mp hm with e | e
    · exact hqp ((h.hp q).mp e)
    · exact hq4 e
  have hq5' : q ∉ R5.faulty := fun hm => hq5 ((h.hT5 q).mp hm)
  have hq0 : g q ≠ 0 := fun e => hqp ((h.hp q).mp e)
  rw [Run.out_of_correct A R4 hq4', Run.out_of_correct A R5 hq5',
    rho4_st_eq_rho5 h T (y := q) (by
      have := h.hg q; omega) τ' (by omega)]

/-- `ρ₄ ∼_{P₁ ∪ P₂ ∪ P₅} ρ₃` up to time `T`: `P₄` behaves towards them as in `ρ₃`, `p` is silent
after round 1 in both, and the round-2+ messages of `P₃` (correct but slow in `ρ₄`, crashed in
`ρ₃`) arrive after `T`. -/
theorem rho4_st_eq_rho3 (hD : 0 < D) (T : ℕ) :
    ∀ τ ≤ T, ∀ y ∈ {y | g y = 1 ∨ g y = 2 ∨ g y = 5},
      (rho4 A D g p I a b T5 (rho3 A D F3 J r3) T).st A τ y = (rho3 A D F3 J r3).st A τ y := by
  set R4 := rho4 A D g p I a b T5 (rho3 A D F3 J r3) T
  set R3 := rho3 A D F3 J r3
  refine R4.st_eq_of_inbox_eq A (ref := fun _ => R3) ?_ ?_
  · intro y hy
    have : y ≠ p := h.ne_p (by simp at hy; omega)
    exact (h.hJ y this).symm
  intro τ hτ ih y hy
  simp only [Set.mem_ofPred_eq] at hy
  apply Run.inbox_eq_of_dlv_eq
  intro q τ' hτ'
  simp only [Run.dlv]
  have hd3 : R3.dl q τ' y = nextRound D τ' := rfl
  have hd4 : R4.dl q τ' y = if D ≤ τ' ∧ ((g q = 3 ∧ g y ≠ 3) ∨ (g q = 5 ∧ g y = 3)) then
      max (nextRound D τ') (T + 2 * D + 1) else nextRound D τ' := rfl
  have hq3F : g q = 3 → q ∈ R3.faulty := fun e => (h.hF3 q).mpr (Or.inr e)
  -- delayed messages of `P₃`
  by_cases hdel : g q = 3 ∧ D ≤ τ'
  · have e4 : R4.dl q τ' y ≠ τ := by
      rw [hd4, ite_eq_left ⟨hdel.2, Or.inl ⟨hdel.1, by omega⟩⟩]
      have := le_max_right (nextRound D τ') (T + 2 * D + 1); omega
    have : R3.out A q τ' y = [] := by
      rw [Run.out_of_faulty A R3 (hq3F hdel.1)]
      simp [R3, templateRun, show ¬ τ' < D by omega]
    simp [e4, this]
  have e4 : R4.dl q τ' y = R3.dl q τ' y := by
    rw [hd4, hd3, ite_eq_right (by omega)]
  rw [e4]
  congr 1
  -- round 1
  by_cases h1 : τ' < D
  · simp only [R4, R3, rho4, rho3]
    rw [templateRun_out_early sched_rho4 h1, templateRun_out_early roundSched_nextRound h1]
    congr 1
    by_cases hqp : q = p
    · subst hqp
      have h4 : q ∈ F4 g := mem_F4.mpr (Or.inl h.gp)
      have h3 : q ∈ F3 := (h.hF3 q).mpr (Or.inl h.gp)
      rcases hy with e | e | e
      · simp [templateEff, h4, h3, e, h.hr3a y (Or.inl e)]
      · simp [templateEff, h4, h3, e, h.hr3a y (Or.inr e)]
      · simp [templateEff, h4, h3, e, h.hr3b y (Or.inr e)]
    · have h4 : templateEff (F4 g) I (fun q x => if q = p then (if g x = 5 then some b else some a)
          else some (I q)) q y = some (I q) := by
        unfold templateEff; split_ifs <;> simp [hqp]
      rw [h4]
      unfold templateEff
      split_ifs with h3
      · have := (h.hF3 q).mp h3
        rw [h.hr3 q (by
          rcases this with e | e
          · exact absurd ((h.hp q).mp e) hqp
          · exact e)]
      · rw [h.hJ q hqp]
  -- later rounds
  have hqp' : g q ≠ 0 → q ≠ p := h.ne_p
  by_cases hqp : q = p
  · subst hqp
    rw [Run.out_of_faulty A R4 (mem_F4.mpr (Or.inl h.gp)),
      Run.out_of_faulty A R3 ((h.hF3 q).mpr (Or.inl h.gp))]
    simp [R4, R3, rho4, templateRun, h1, show g y ≠ 3 by omega]
  by_cases hq4 : g q = 4
  · rw [Run.out_of_faulty A R4 (mem_F4.mpr (Or.inr hq4))]
    have hq3 : q ∉ R3.faulty := fun hm => by have := (h.hF3 q).mp hm; omega
    simp [R4, rho4, templateRun, h1, hqp, show g y ≠ 3 by omega, show τ' ≤ T by omega]
    rfl
  have hq0 : g q ≠ 0 := fun e => hqp ((h.hp q).mp e)
  have hq3 : g q ≠ 3 := fun e => hdel ⟨e, by omega⟩
  have hq4' : q ∉ R4.faulty := fun hm => by have := mem_F4.mp hm; omega
  have hq3' : q ∉ R3.faulty := fun hm => by have := (h.hF3 q).mp hm; omega
  rw [Run.out_of_correct A R4 hq4', Run.out_of_correct A R3 hq3',
    ih q (by simp; have := h.hg q; omega) τ' hτ']

omit h in
/-- `ρ₄` is admissible: at most `f` faults (`{p} ∪ P₄`), and every message between correct
processes is delivered within `δ` after GST `= T + 2δ + 1`. -/
theorem rho4_valid {f : ℕ} (hD : 0 < D) (T : ℕ) (hf : (F4 g).card ≤ f) :
    (rho4 A D g p I a b T5 (rho3 A D F3 J r3) T).Valid f D where
  card_faulty := hf
  dl_ge q τ x _ _ := by
    change τ ≤ (if _ then _ else _)
    have := le_nextRound (D := D) (τ := τ) hD
    split_ifs
    · exact this.le.trans (le_max_left _ _)
    · exact this.le
  dl_le q τ x _ _ := by
    change (if _ then _ else _) ≤ max τ (T + 2 * D + 1) + D
    have := nextRound_le (D := D) (τ := τ)
    have h1 := le_max_left τ (T + 2 * D + 1)
    have h2 := le_max_right τ (T + 2 * D + 1)
    split_ifs
    · apply max_le <;> omega
    · omega

/-- `ρ₄` respects unforgeability: Byzantine messages are round-1 messages (own signatures only)
or replays of `ρ₅` (to `P₃`, up to round 2) and of `ρ₃` (to the others, up to `T`). -/
theorem rho4_authValid (hU : A.Unforging Au) (hD : 0 < D) (T : ℕ) :
    (rho4 A D g p I a b T5 (rho3 A D F3 J r3) T).AuthValid Au A := by
  set R4 := rho4 A D g p I a b T5 (rho3 A D F3 J r3) T
  set R3 := rho3 A D F3 J r3
  set R5 := tsRun (M := M) A D (Function.update I p a) T5
  have hpF : p ∈ R4.faulty := mem_F4.mpr (Or.inl h.gp)
  -- replay of `ρ₅` up to time `2D`
  have rep5 := Run.tokens_replay (Au := Au) hU (Ri := R5) (R' := R4) (T := 2 * D) (by
    intro q σ r' hσ
    by_cases hqp : q = p
    · subst hqp
      exact Or.inr (Or.inl ⟨hpF, fun hm => by have := (h.hT5 q).mp hm; rw [h.gp] at this; omega⟩)
    by_cases hq4 : g q = 4
    · exact Or.inr (Or.inl ⟨mem_F4.mpr (Or.inr hq4), fun hm => by have := (h.hT5 q).mp hm; omega⟩)
    have hq0 : g q ≠ 0 := fun e => hqp ((h.hp q).mp e)
    have hq4' : q ∉ R4.faulty := fun hm => by have := mem_F4.mp hm; omega
    by_cases hq5 : g q = 5
    · by_cases hσ' : σ < D
      · left
        refine ⟨hq4', ?_⟩
        simp only [R4, R5, rho4]
        rw [tsRun_eq, templateRun_out_early sched_rho4 hσ',
          templateRun_out_early roundSched_nextRound hσ']
        congr 1
        have h5 : q ∈ T5 := (h.hT5 q).mpr hq5
        simp [templateEff, h5, hqp, show q ∉ F4 g from hq4']
      · right; right
        intro m hm
        rw [Run.out_of_faulty A R5 ((h.hT5 q).mpr hq5)] at hm
        simp [R5, tsRun, hσ'] at hm
    · left
      refine ⟨hq4', ?_⟩
      have hq5' : q ∉ R5.faulty := fun hm => hq5 ((h.hT5 q).mp hm)
      rw [Run.out_of_correct A R4 hq4', Run.out_of_correct A R5 hq5',
        rho4_st_eq_rho5 h T (y := q) (by have := h.hg q; omega) σ hσ])
  -- replay of `ρ₃` up to time `T`
  have rep3 := Run.tokens_replay (Au := Au) hU (Ri := R3) (R' := R4) (T := T) (by
    intro q σ r' hσ
    by_cases hqp : q = p
    · subst hqp
      right; right
      intro m hm k hk
      rw [Run.out_of_faulty A R3 ((h.hF3 q).mpr (Or.inl h.gp))] at hm
      simp only [R3, templateRun] at hm
      split_ifs at hm
      · rw [round1_tokens A hU hm hk]; exact hpF
      · simp at hm
    by_cases hq4 : g q = 4
    · exact Or.inr (Or.inl ⟨mem_F4.mpr (Or.inr hq4), fun hm => by have := (h.hF3 q).mp hm; omega⟩)
    have hq0 : g q ≠ 0 := fun e => hqp ((h.hp q).mp e)
    have hq4' : q ∉ R4.faulty := fun hm => by have := mem_F4.mp hm; omega
    by_cases hq3 : g q = 3
    · by_cases hσ' : σ < D
      · left
        refine ⟨hq4', ?_⟩
        simp only [R4, R3, rho4, rho3]
        rw [templateRun_out_early sched_rho4 hσ', templateRun_out_early roundSched_nextRound hσ']
        congr 1
        have h3 : q ∈ F3 := (h.hF3 q).mpr (Or.inr hq3)
        simp [templateEff, h3, show q ∉ F4 g from hq4', h.hr3 q hq3]
      · right; right
        intro m hm
        rw [Run.out_of_faulty A R3 ((h.hF3 q).mpr (Or.inr hq3))] at hm
        simp [R3, templateRun, hσ'] at hm
    · left
      refine ⟨hq4', ?_⟩
      have hq3' : q ∉ R3.faulty := fun hm => by have := (h.hF3 q).mp hm; omega
      rw [Run.out_of_correct A R4 hq4', Run.out_of_correct A R3 hq3',
        rho4_st_eq_rho3 h hD T σ hσ q (by simp; have := h.hg q; omega)])
  intro bb hbb τ r _ m hm k hk
  have hbb' := mem_F4.mp hbb
  simp only [R4, rho4, templateRun] at hm
  by_cases hτ : τ < D
  · rw [ite_eq_left hτ] at hm
    left; rw [round1_tokens A hU hm hk]; exact hbb
  rw [ite_eq_right hτ] at hm
  by_cases hbp : bb = p
  · subst hbp
    rw [ite_eq_left rfl] at hm
    split_ifs at hm with h1
    · exact rep5 τ (by omega) bb r m hm k hk
    · simp at hm
  rw [ite_eq_right hbp] at hm
  split_ifs at hm with h1 h2 h3
  · exact rep5 τ (by omega) bb r m hm k hk
  · simp at hm
  · exact rep3 τ h3 bb r m hm k hk
  · simp at hm

/-- **Core of the two-step lower bound** (`ρ₅ ∼_{P₃} ρ₄ ∼_{P₁ ∪ P₂ ∪ P₅} ρ₃`): if the algorithm
satisfies agreement in partially synchronous runs with at most `f` faults, the decision of a
process of `P₁ ∪ P₂ ∪ P₅` in `ρ₃` equals the decision within two rounds of a process of `P₃` in
the two-step execution `ρ₅`. -/
theorem decision_eq (hU : A.Unforging Au)
    (hag : ∀ R : Run P M V, R.Valid f D → R.AuthValid Au A → ∀ x ∉ R.faulty, ∀ y ∉ R.faulty,
      ∀ v w, R.Decides A x v → R.Decides A y w → v = w)
    (hD : 0 < D) (hf : (F4 g).card ≤ f) {x3 : P} (hx3 : g x3 = 3) {v : V}
    (h5 : (tsRun A D (Function.update I p a) T5).DecidesBy A x3 v (2 * D + 1))
    {x1 : P} (hx1 : g x1 = 1 ∨ g x1 = 2 ∨ g x1 = 5) {w : V}
    (h3 : (rho3 A D F3 J r3).Decides A x1 w) : v = w := by
  obtain ⟨τ1, hτ1⟩ := h3
  obtain ⟨τ5, hτ5, hd5⟩ := h5
  have hx1F : x1 ∉ (rho4 A D g p I a b T5 (rho3 A D F3 J r3) τ1).faulty := fun hm => by
    have := mem_F4.mp hm; omega
  have hx3F : x3 ∉ (rho4 A D g p I a b T5 (rho3 A D F3 J r3) τ1).faulty := fun hm => by
    have := mem_F4.mp hm; omega
  refine hag _ (rho4_valid hD τ1 hf) (rho4_authValid h hU hD τ1) x3 hx3F x1 hx1F v w
    ⟨τ5, ?_⟩ ⟨τ1, ?_⟩
  · rw [rho4_st_eq_rho5_P3 h hD τ1 hx3 τ5 hτ5]; exact hd5
  · rw [rho4_st_eq_rho3 h hD τ1 τ1 le_rfl x1 (by simpa using hx1)]; exact hτ1

end side

section rho3

variable {A : Algorithm P M S V V} {Au : Auth P M K} {f D : ℕ} {F3 : Finset P} {J : P → V}
  {r3 : P → P → Option V}

omit [Fintype P] [DecidableEq P] in
/-- `ρ₃` is admissible (synchronous, `gst = 0`). -/
theorem rho3_valid (hD : 0 < D) (hf : F3.card ≤ f) : (rho3 A D F3 J r3).Valid f D where
  card_faulty := hf
  dl_ge _ _ _ _ _ := (le_nextRound hD).le
  dl_le _ _ _ _ _ := nextRound_le.trans (by simp [rho3, templateRun])

set_option linter.unusedFintypeInType false in
/-- `ρ₃` respects unforgeability (Byzantine processes only send round-1 messages). -/
theorem rho3_authValid (hU : A.Unforging Au) : (rho3 A D F3 J r3).AuthValid Au A := by
  intro bb hbb τ r _ m hm k hk
  simp only [rho3, templateRun] at hm
  split_ifs at hm
  · left; rw [round1_tokens A hU hm hk]; exact hbb
  · simp at hm

end rho3

end TwoStepLB

end Cslib.Byzantine.PartialSync
