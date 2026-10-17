/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Auth

/-!
# Merging two runs: the split-brain run of partition arguments

The classical partition argument of the partially synchronous model (Dwork, Lynch and Stockmeyer)
takes two runs `R₁`, `R₂` and builds a third run in which the processes correct in `R₁` only
cannot distinguish it from `R₁`, and the processes correct in `R₂` only cannot distinguish it from
`R₂`, up to a time `T`. `Run.merge A R₁ R₂ T` is this run:

* the processes correct in **both** runs are Byzantine: up to `T` they replay their `R₂`-messages
  towards the `R₂`-only side and their `R₁`-messages towards everybody else, afterwards they are
  silent;
* all other processes are correct (with their `R₁`-proposal if correct in `R₁`, else their
  `R₂`-proposal);
* `gst = T + 1`: up to `T`, a batch between two processes correct in `R₁` (resp. `R₂`) keeps its
  `R₁`- (resp. `R₂`-) delivery time, capped at `T + 1`; every other batch sent up to `T` is delayed
  to `T + 1`; after `T` the run is synchronous with zero delay.

## Main statements

* `Run.merge_valid`: the merged run satisfies the model constraints for any `δ`, given the bound on
  the number of processes correct in both runs (`Run.merge_valid_of_forall_mem`: when there are
  none).
* `Run.merge_st_left`, `Run.merge_st_right` (indistinguishability): if `R₁` (resp. `R₂`) is
  canonical, the processes correct in `R₁` only (resp. `R₂` only) have the same states as in `R₁`
  (resp. `R₂`) up to time `T`; `Run.merge_decides_left`, `Run.merge_decides_right` transfer
  decisions.
* `Run.merge_authValid`: if both runs are canonical and the algorithm is unforging, the merged run
  respects unforgeability (`Run.tokens_replay`); `Run.merge_authValid_of_forall_mem`: without
  unforgeability when no process is correct in both runs.

`Run.extend` (`Constructions.lean`) is the one-sided variant: a canonical run is extended to a new
input configuration, the new processes waking up after `T`.

Typical uses: the merging argument of [CivitEtAl2023] for validity properties; the merge with an
isolated process; the split-brain run of hybrid approximate agreement (Theorem 5.1 of
Ghinea, Liu-Zhang and Wattenhofer); impossibility of partially synchronous Byzantine broadcast
with `n ∈ {2, 3}` processes.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P]

namespace Run

variable (A : Algorithm P M S VI VO)

/-- The run merging `R₁` and `R₂` up to time `T` (see the module docstring): the processes
correct in both runs are Byzantine and replay their `R₂`-messages towards the processes correct
in `R₂` only and their `R₁`-messages towards the others; communication across the two sides is
delayed past `T`, and `gst = T + 1`. -/
def merge (R₁ R₂ : Run P M VI) (T : ℕ) : Run P M VI where
  faulty := R₁.faultyᶜ ∩ R₂.faultyᶜ
  inp p := if p ∉ R₁.faulty then R₁.inp p else R₂.inp p
  gst := T + 1
  byz q τ p := if τ ≤ T then
      (if p ∉ R₂.faulty ∧ p ∈ R₁.faulty then R₂.out A q τ p else R₁.out A q τ p) else []
  dl q τ p := if τ ≤ T then
      (if q ∉ R₁.faulty ∧ p ∉ R₁.faulty then min (R₁.dl q τ p) (T + 1)
       else if q ∉ R₂.faulty ∧ p ∉ R₂.faulty then min (R₂.dl q τ p) (T + 1) else T + 1)
    else τ

variable {A} {R₁ R₂ : Run P M VI} {T : ℕ}

/-- The Byzantine processes of the merged run are those correct in both runs. -/
@[simp] theorem mem_merge_faulty {p : P} :
    p ∈ (R₁.merge A R₂ T).faulty ↔ p ∉ R₁.faulty ∧ p ∉ R₂.faulty := by
  simp [merge]

/-- The merged run stabilizes right after `T`. -/
@[simp] theorem merge_gst : (R₁.merge A R₂ T).gst = T + 1 := rfl

/-- Processes correct in `R₁` keep their `R₁`-proposal. -/
theorem merge_inp_of_notMem {p : P} (hp : p ∉ R₁.faulty) :
    (R₁.merge A R₂ T).inp p = R₁.inp p := by
  simp [merge, hp]

/-- Processes faulty in `R₁` get their `R₂`-proposal. -/
theorem merge_inp_of_mem {p : P} (hp : p ∈ R₁.faulty) :
    (R₁.merge A R₂ T).inp p = R₂.inp p := by
  simp [merge, hp]

/-- If every process is faulty in one of the two runs, nobody is Byzantine in the merged run. -/
theorem merge_faulty_eq_empty (h : ∀ p, p ∈ R₁.faulty ∨ p ∈ R₂.faulty) :
    (R₁.merge A R₂ T).faulty = ∅ := by
  ext p; have := h p; simp only [mem_merge_faulty, notMem_empty, iff_false]; tauto

/-- The merged run satisfies the model constraints (for any `δ`, as `gst = T + 1`), provided at
most `t` processes are correct in both runs and both runs deliver batches between their correct
processes no earlier than they are sent. -/
theorem merge_valid {t δ : ℕ} (hcard : (R₁.faultyᶜ ∩ R₂.faultyᶜ).card ≤ t)
    (h₁ : ∀ q τ p, q ∉ R₁.faulty → p ∉ R₁.faulty → τ ≤ R₁.dl q τ p)
    (h₂ : ∀ q τ p, q ∉ R₂.faulty → p ∉ R₂.faulty → τ ≤ R₂.dl q τ p) :
    (R₁.merge A R₂ T).Valid t δ where
  card_faulty := hcard
  dl_ge q τ p _ _ := by
    simp only [merge]
    split_ifs with h0 h1 h2
    · exact le_min (h₁ q τ p h1.1 h1.2) (by omega)
    · exact le_min (h₂ q τ p h2.1 h2.2) (by omega)
    · omega
    · exact le_rfl
  dl_le q τ p _ _ := by
    simp only [merge]
    split_ifs <;> omega

/-- `merge_valid` when every process is faulty in one of the two runs (so the merged run has no
Byzantine process). -/
theorem merge_valid_of_forall_mem {t δ : ℕ} (h : ∀ p, p ∈ R₁.faulty ∨ p ∈ R₂.faulty)
    (h₁ : ∀ q τ p, q ∉ R₁.faulty → p ∉ R₁.faulty → τ ≤ R₁.dl q τ p)
    (h₂ : ∀ q τ p, q ∉ R₂.faulty → p ∉ R₂.faulty → τ ≤ R₂.dl q τ p) :
    (R₁.merge A R₂ T).Valid t δ :=
  merge_valid (by
    have : (R₁.merge A R₂ T).faulty.card = 0 := by rw [merge_faulty_eq_empty h, card_empty]
    exact this ▸ Nat.zero_le t) h₁ h₂

/-- **Indistinguishability, left side.** If `R₁` is canonical, the processes correct in `R₁` but
faulty in `R₂` cannot distinguish the merged run from `R₁` up to time `T`. -/
theorem merge_st_left (hc₁ : R₁.Canonical) :
    ∀ τ ≤ T, ∀ p, p ∉ R₁.faulty → p ∈ R₂.faulty → (R₁.merge A R₂ T).st A τ p = R₁.st A τ p := by
  intro τ hτ p hp1 hp2
  refine (R₁.merge A R₂ T).st_eq_of_inbox_eq A (ref := fun _ => R₁)
    (X := {p | p ∉ R₁.faulty ∧ p ∈ R₂.faulty}) ?_ ?_ τ hτ p ⟨hp1, hp2⟩
  · rintro p ⟨hp, -⟩; simp [merge, hp]
  · rintro τ hτ ih p ⟨hp1, hp2⟩
    refine (R₁.merge A R₂ T).inbox_eq_of_dlv_eq A fun q τ' hτ' => ?_
    by_cases hq : q ∈ R₁.faulty
    · rw [dlv_eq_nil_of_ne A _ (by simp [merge, hq, hp2, show τ' ≤ T by omega]; omega)]
      simp [dlv, out_eq_nil_of_canonical A hc₁ hq]
    · have hdl : (R₁.merge A R₂ T).dl q τ' p = min (R₁.dl q τ' p) (T + 1) := by
        simp [merge, hq, hp1, show τ' ≤ T by omega]
      have hiff : (min (R₁.dl q τ' p) (T + 1) = τ) ↔ R₁.dl q τ' p = τ := by omega
      simp only [dlv, hdl, hiff]
      split_ifs
      · by_cases hq2 : q ∈ R₂.faulty
        · rw [out_of_correct A _ (by simp [hq2]), out_of_correct A _ hq, ih q ⟨hq, hq2⟩ τ' hτ']
        · rw [out_of_faulty A _ (mem_merge_faulty.2 ⟨hq, hq2⟩)]
          simp [merge, hp2, show τ' ≤ T by omega]
      · rfl

/-- **Indistinguishability, right side.** If `R₂` is canonical, the processes correct in `R₂` but
faulty in `R₁` cannot distinguish the merged run from `R₂` up to time `T`. -/
theorem merge_st_right (hc₂ : R₂.Canonical) :
    ∀ τ ≤ T, ∀ p, p ∈ R₁.faulty → p ∉ R₂.faulty → (R₁.merge A R₂ T).st A τ p = R₂.st A τ p := by
  intro τ hτ p hp1 hp2
  refine (R₁.merge A R₂ T).st_eq_of_inbox_eq A (ref := fun _ => R₂)
    (X := {p | p ∈ R₁.faulty ∧ p ∉ R₂.faulty}) ?_ ?_ τ hτ p ⟨hp1, hp2⟩
  · rintro p ⟨hp, -⟩; simp [merge, hp]
  · rintro τ hτ ih p ⟨hp1, hp2⟩
    refine (R₁.merge A R₂ T).inbox_eq_of_dlv_eq A fun q τ' hτ' => ?_
    by_cases hq : q ∈ R₂.faulty
    · rw [dlv_eq_nil_of_ne A _ (by simp [merge, hq, hp1, show τ' ≤ T by omega]; omega)]
      simp [dlv, out_eq_nil_of_canonical A hc₂ hq]
    · have hdl : (R₁.merge A R₂ T).dl q τ' p = min (R₂.dl q τ' p) (T + 1) := by
        simp [merge, hq, hp1, hp2, show τ' ≤ T by omega]
      have hiff : (min (R₂.dl q τ' p) (T + 1) = τ) ↔ R₂.dl q τ' p = τ := by omega
      simp only [dlv, hdl, hiff]
      split_ifs
      · by_cases hq1 : q ∈ R₁.faulty
        · rw [out_of_correct A _ (by simp [hq1]), out_of_correct A _ hq, ih q ⟨hq1, hq⟩ τ' hτ']
        · rw [out_of_faulty A _ (mem_merge_faulty.2 ⟨hq1, hq⟩)]
          simp [merge, hp2, hp1, show τ' ≤ T by omega]
      · rfl

/-- A decision taken by time `T` by a process correct in `R₁` only is also taken in the merged
run. -/
theorem merge_decides_left (hc₁ : R₁.Canonical) {p : P} (hp1 : p ∉ R₁.faulty)
    (hp2 : p ∈ R₂.faulty) {τ : ℕ} (hτ : τ ≤ T) {v : VO} (h : A.decide p (R₁.st A τ p) = some v) :
    (R₁.merge A R₂ T).Decides A p v :=
  ⟨τ, by rw [merge_st_left hc₁ τ hτ p hp1 hp2]; exact h⟩

/-- A decision taken by time `T` by a process correct in `R₂` only is also taken in the merged
run. -/
theorem merge_decides_right (hc₂ : R₂.Canonical) {p : P} (hp1 : p ∈ R₁.faulty)
    (hp2 : p ∉ R₂.faulty) {τ : ℕ} (hτ : τ ≤ T) {v : VO} (h : A.decide p (R₂.st A τ p) = some v) :
    (R₁.merge A R₂ T).Decides A p v :=
  ⟨τ, by rw [merge_st_right hc₂ τ hτ p hp1 hp2]; exact h⟩

/-- **Unforgeability.** If both runs are canonical and the algorithm is unforging, the Byzantine
processes of the merged run only replay messages they sent as correct processes in `R₁` / `R₂`,
so the merged run respects unforgeability. -/
theorem merge_authValid {Au : Auth P M K} (hU : A.Unforging Au) (hc₁ : R₁.Canonical)
    (hc₂ : R₂.Canonical) : (R₁.merge A R₂ T).AuthValid Au A := by
  intro b _ τ r _ m hm x hx
  simp only [merge] at hm
  split_ifs at hm with hτ hr'
  · refine tokens_replay hU (Ri := R₂) (T := T) (fun q σ r' hσ => ?_) τ hτ b r m hm x hx
    by_cases hq : q ∈ R₂.faulty
    · right; right; intro m' hm'
      simp [out_eq_nil_of_canonical A hc₂ hq] at hm'
    · by_cases hq1 : q ∈ R₁.faulty
      · left
        have hqR : q ∉ (R₁.merge A R₂ T).faulty := by simp [hq1]
        refine ⟨hqR, ?_⟩
        rw [out_of_correct A _ hqR, out_of_correct A _ hq, merge_st_right hc₂ σ hσ q hq1 hq]
      · right; left; exact ⟨mem_merge_faulty.2 ⟨hq1, hq⟩, hq⟩
  · refine tokens_replay hU (Ri := R₁) (T := T) (fun q σ r' hσ => ?_) τ hτ b r m hm x hx
    by_cases hq : q ∈ R₁.faulty
    · right; right; intro m' hm'
      simp [out_eq_nil_of_canonical A hc₁ hq] at hm'
    · by_cases hq2 : q ∈ R₂.faulty
      · left
        have hqR : q ∉ (R₁.merge A R₂ T).faulty := by simp [hq2]
        refine ⟨hqR, ?_⟩
        rw [out_of_correct A _ hqR, out_of_correct A _ hq, merge_st_left hc₁ σ hσ q hq hq2]
      · right; left; exact ⟨mem_merge_faulty.2 ⟨hq, hq2⟩, hq⟩
  · simp at hm

/-- If every process is faulty in one of the two runs, the merged run has no Byzantine process
and hence respects unforgeability (for every algorithm). -/
theorem merge_authValid_of_forall_mem {Au : Auth P M K}
    (h : ∀ p, p ∈ R₁.faulty ∨ p ∈ R₂.faulty) : (R₁.merge A R₂ T).AuthValid Au A := by
  intro b hb
  simp [merge_faulty_eq_empty (A := A) (T := T) h] at hb

end Run

end Cslib.Byzantine.PartialSync
