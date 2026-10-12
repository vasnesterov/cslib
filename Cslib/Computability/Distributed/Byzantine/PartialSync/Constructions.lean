/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Consensus

/-!
# Standard run constructions

* `canonRun c d`: the canonical, synchronous (`gst = 0`, zero delay) run corresponding to the
  configuration `c`: processes outside `π(c)` are faulty and silent.
* `Run.extend`: given a canonical run `R` and a configuration `c'` agreeing with `R` on common
  processes, a run with input configuration `c'` that is indistinguishable from `R` up to time
  `T` for the processes correct in both ("the other processes wake up late": all their messages
  are delayed past `T`, which is legal since `gst := T + 1`). The processes outside `π(c')` are
  Byzantine: up to `T` they replay their messages of `R`, afterwards they are silent.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S VI VO : Type*} [Fintype P] [DecidableEq P]

/-- The canonical synchronous run for configuration `c` (`d` is a dummy proposal for the
processes outside `π(c)`). -/
def canonRun (c : Config P VI) (d : VI) : Run P M VI where
  faulty := c.procsᶜ
  inp p := (c p).getD d
  gst := 0
  byz _ _ _ := []
  dl _ τ _ := τ

namespace canonRun

variable (c : Config P VI) (d : VI)

theorem valid {t : ℕ} (hc : IsInputConfig t c) (δ : ℕ) : (canonRun (M := M) c d).Valid t δ where
  card_faulty := by
    simp only [canonRun, card_compl]
    unfold IsInputConfig at hc
    have := c.procs.card_le_univ
    omega
  dl_ge _ _ _ _ _ := le_rfl
  dl_le _ τ _ _ _ := by simp [canonRun]

theorem canonical : (canonRun (M := M) c d).Canonical := fun _ _ _ _ => rfl

theorem inputConf : (canonRun (M := M) c d).inputConf = c := by
  funext p
  by_cases hp : c p = none
  · simp [Run.inputConf, canonRun, hp]
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hp
    simp [Run.inputConf, canonRun, hv]

end canonRun

/-- The run in which `Q` is the only correct process (proposing `v`) and every other process is
faulty and silent: `Q` runs *in isolation*, receiving only its own messages (with zero delay).
Not a valid run in general (too many faults); used as a reference for indistinguishability. -/
def isoRun (Q : P) (v : VI) : Run P M VI where
  faulty := {Q}ᶜ
  inp _ := v
  gst := 0
  byz _ _ _ := []
  dl _ τ _ := τ

theorem isoRun_canonical (Q : P) (v : VI) : (isoRun (M := M) Q v).Canonical :=
  fun _ _ _ _ => rfl

theorem isoRun_correct (Q : P) (v : VI) : Q ∉ (isoRun (M := M) Q v).faulty := by
  simp [isoRun]

namespace Run

variable (A : Algorithm P M S VI VO)

/-- The extension of a run `R` to configuration `c'` after time `T` (see module docstring). -/
def extend (R : Run P M VI) (c' : Config P VI) (T : ℕ) : Run P M VI where
  faulty := c'.procsᶜ
  inp p := (c' p).getD (R.inp p)
  gst := T + 1
  byz q τ p := if τ ≤ T then R.out A q τ p else []
  dl q τ p := if q ∉ R.faulty ∧ p ∉ R.faulty ∧ τ ≤ T then min (R.dl q τ p) (T + 1)
    else max τ (T + 1)

variable {A} {t δ : ℕ}

theorem extend_valid {R : Run P M VI} (hR : R.Valid t δ) {c' : Config P VI}
    (hc' : IsInputConfig t c') (T : ℕ) : (R.extend A c' T).Valid t δ where
  card_faulty := by
    simp only [extend, card_compl]
    unfold IsInputConfig at hc'
    have := c'.procs.card_le_univ
    omega
  dl_ge q τ p _ _ := by
    simp only [extend]
    split_ifs with h
    · exact le_min (hR.dl_ge q τ p h.1 h.2.1) (by omega)
    · exact le_max_left _ _
  dl_le q τ p _ _ := by
    simp only [extend]
    split_ifs with h
    · exact (min_le_right _ _).trans (by omega)
    · omega

theorem extend_inputConf (R : Run P M VI) (c' : Config P VI) (T : ℕ) :
    (R.extend A c' T).inputConf = c' := by
  funext p
  by_cases hp : c' p = none
  · simp [Run.inputConf, extend, hp]
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hp
    simp [Run.inputConf, extend, hv]

/-- Processes correct in both `R` and `R.extend A c' T` cannot distinguish them up to `T`. -/
theorem extend_st {R : Run P M VI} (hcan : R.Canonical)
    {c' : Config P VI} (hsim : ∀ p ∉ R.faulty, c' p ≠ none → c' p = some (R.inp p)) (T : ℕ) :
    ∀ τ ≤ T, ∀ p, p ∉ R.faulty → c' p ≠ none → (R.extend A c' T).st A τ p = R.st A τ p := by
  intro τ hτ p hp hp'
  refine (R.extend A c' T).st_eq_of_inbox_eq A (ref := fun _ => R)
    (X := {p | p ∉ R.faulty ∧ c' p ≠ none}) ?_ ?_ τ hτ p ⟨hp, hp'⟩
  · rintro p ⟨hp, hp'⟩
    simp [extend, hsim p hp hp']
  · rintro τ hτ ih p ⟨hp, hp'⟩
    refine (R.extend A c' T).inbox_eq_of_dlv_eq A fun q τ' hτ' => ?_
    by_cases hq : q ∈ R.faulty
    · rw [dlv_eq_nil_of_ne, dlv]
      · simp [out_eq_nil_of_canonical A hcan hq]
      · simp only [extend, hq, not_true_eq_false, false_and, ite_false]
        omega
    · have hdl : (R.extend A c' T).dl q τ' p = min (R.dl q τ' p) (T + 1) := by
        simp only [extend, hq, hp, not_false_eq_true, true_and, show τ' ≤ T by omega, ite_true]
      simp only [dlv, hdl]
      have : (min (R.dl q τ' p) (T + 1) = τ) ↔ R.dl q τ' p = τ := by omega
      simp only [this]
      split_ifs
      · by_cases hq' : c' q = none
        · rw [out_of_faulty A _ (by simp [extend, hq'])]
          simp [extend, show τ' ≤ T by omega]
        · rw [out_of_correct A _ (by simp [extend, Option.isSome_iff_ne_none, hq']),
            out_of_correct A _ hq, ih q ⟨hq, hq'⟩ τ' hτ']
      · rfl

end Run

end Cslib.Byzantine.PartialSync
