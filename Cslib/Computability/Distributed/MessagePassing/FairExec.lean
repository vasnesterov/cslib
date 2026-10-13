/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.MessagePassing.Async

/-!
# Finite runs and fair executions

`Protocol.runFrom C ss` runs a list of steps from `C` and returns the final configuration and the
history labels. A finite run that ends in a configuration where no step of any process (internal
action or reception) is enabled extends — by stuttering — to an infinite **fair** execution
(`exists_fair_exec_of_quiescent`). This is used to check that fairness hypotheses are not
vacuous.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Cslib.AsyncMP.Protocol

open Cslib.SharedMemory

variable {P : Type} {A : ObjSpec} {L M Act : Type} [DecidableEq P] [DecidableEq M]
variable (Pr : Protocol P A L M Act)

/-- Run a list of steps. -/
def runFrom (C : Config P L M) : List (Step P A M Act) →
    Option (Config P L M × List (Label P A))
  | [] => some (C, [])
  | s :: ss => (Pr.step C s).bind fun x =>
      (runFrom x.1 ss).map fun y => (y.1, x.2.toList ++ y.2)

variable {Pr}

lemma runFrom_append (C : Config P L M) (ss ss' : List (Step P A M Act)) :
    Pr.runFrom C (ss ++ ss') = (Pr.runFrom C ss).bind fun x =>
      (Pr.runFrom x.1 ss').map fun y => (y.1, x.2 ++ y.2) := by
  induction ss generalizing C with
  | nil => simp [runFrom]
  | cons s ss ih =>
    simp only [List.cons_append, runFrom, ih]
    cases Pr.step C s with
    | none => rfl
    | some x =>
      simp only [Option.bind_some]
      cases Pr.runFrom x.1 ss with
      | none => rfl
      | some y =>
        simp only [Option.map_some, Option.bind_some]
        cases Pr.runFrom y.1 ss' <;> simp [List.append_assoc]

lemma runFrom_singleton (C : Config P L M) (s : Step P A M Act) :
    Pr.runFrom C [s] = (Pr.step C s).map fun x => (x.1, x.2.toList) := by
  simp only [runFrom]
  cases Pr.step C s <;> simp

lemma runFrom_reach {C : Config P L M} {h : List (Label P A)} (hr : Pr.Reach C h)
    {ss : List (Step P A M Act)} {C' : Config P L M} {h' : List (Label P A)}
    (hrun : Pr.runFrom C ss = some (C', h')) : Pr.Reach C' (h ++ h') := by
  induction ss generalizing C h h' with
  | nil =>
    simp only [runFrom, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun; simpa using hr
  | cons s ss ih =>
    simp only [runFrom, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hrun
    obtain ⟨⟨C₁, ℓ⟩, h1, ⟨C₂, h₂⟩, h2, he⟩ := hrun
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := ih (Reach.step hr h1) h2
    simpa [List.append_assoc] using this

lemma runFrom_take_isSome {C : Config P L M} {ss : List (Step P A M Act)}
    (h : (Pr.runFrom C ss).isSome) (t : ℕ) : (Pr.runFrom C (ss.take t)).isSome := by
  rw [← List.take_append_drop t ss, runFrom_append] at h
  cases h' : Pr.runFrom C (ss.take t) with
  | none => rw [h'] at h; simp at h
  | some _ => rfl

/-- A finite run ending in a configuration where no step of any process is enabled extends, by
stuttering, to an infinite fair execution with the same history. -/
theorem exists_fair_exec_of_quiescent {ss : List (Step P A M Act)} {C : Config P L M}
    {h : List (Label P A)} (hrun : Pr.runFrom Pr.initCfg ss = some (C, h))
    (hq : ∀ (s : Step P A M Act) (p : P), s.owner = some p → ¬ Pr.Enabled C s) :
    ∃ e : Pr.Exec, e.Fair ∧ e.hist ss.length = h ∧ (∀ t ≥ ss.length, e.cfg t = C) ∧
      ∀ t, (e.cfg t).crashed ⊆ C.crashed := by
  -- prefixes of the run
  let R : ℕ → Config P L M × List (Label P A) :=
    fun t => (Pr.runFrom Pr.initCfg (ss.take t)).getD (Pr.initCfg, [])
  have hR : ∀ t, Pr.runFrom Pr.initCfg (ss.take t) = some (R t) := by
    intro t
    have := runFrom_take_isSome (Pr := Pr) (by rw [hrun]; rfl) t
    simp only [R]
    cases h' : Pr.runFrom Pr.initCfg (ss.take t) with
    | none => rw [h'] at this; simp at this
    | some x => rfl
  have hRlen : ∀ t ≥ ss.length, R t = (C, h) := by
    intro t ht
    have := hR t
    rw [List.take_of_length_le ht, hrun] at this
    exact (Option.some.inj this).symm
  have hstep : ∀ t, ∃ ℓ, Pr.step (R t).1 (ss.getD t .skip) = some ((R (t + 1)).1, ℓ) ∧
      (R (t + 1)).2 = (R t).2 ++ ℓ.toList := by
    intro t
    by_cases ht : t < ss.length
    · have h1 := hR (t + 1)
      rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, runFrom_append,
        hR t, Option.bind_some, runFrom_singleton] at h1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
      cases h2 : Pr.step (R t).1 ss[t] with
      | none => rw [h2] at h1; simp at h1
      | some x =>
        rw [h2] at h1
        simp only [Option.map_some, Option.some.injEq] at h1
        refine ⟨x.2, ?_, ?_⟩
        · rw [← h1]
        · rw [← h1]
    · push Not at ht
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ht, Option.getD_none, hRlen t ht,
        hRlen (t + 1) (by omega)]
      exact ⟨none, by simp [step], by simp⟩
  choose lbl hlbl using hstep
  let e : Pr.Exec :=
    { cfg := fun t => (R t).1
      stp := fun t => ss.getD t .skip
      lbl := lbl
      init := by
        have := hR 0
        simp only [List.take_zero, runFrom] at this
        rw [← (Option.some.inj this)]
      step := fun t => (hlbl t).1 }
  have hhist : ∀ t, e.hist t = (R t).2 := by
    intro t
    induction t with
    | zero =>
      have := hR 0
      simp only [List.take_zero, runFrom] at this
      rw [← (Option.some.inj this)]; rfl
    | succ t ih => rw [e.hist_succ, ih, (hlbl t).2]
  have hcr : ∀ t, (R t).1.crashed ⊆ C.crashed := by
    intro t
    obtain ⟨k, hk⟩ : ∃ k, k = ss.length - t := ⟨_, rfl⟩
    induction k generalizing t with
    | zero => rw [hRlen t (by omega)]
    | succ k ih =>
      exact (step_crashed_mono (hlbl t).1).trans (ih (t + 1) (by omega))
  refine ⟨e, ?_, ?_, ?_, hcr⟩
  · intro s p hs _ T hen
    exact absurd (hen (max T ss.length) (le_max_left _ _))
      (by change ¬ Pr.Enabled (R (max T ss.length)).1 s
          rw [hRlen _ (le_max_right _ _)]; exact hq s p hs)
  · rw [hhist, hRlen _ le_rfl]
  · intro t ht; change (R t).1 = C; rw [hRlen t ht]

end Cslib.AsyncMP.Protocol
