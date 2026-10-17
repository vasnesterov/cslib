/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.QuietRuns

/-!
# Synchronous, partially synchronous and asynchronous runs

CSLib's `Run.Valid t δ` is the class of *partially synchronous* runs: at most `t` faults, and every
batch between correct processes sent at `τ` is delivered in `[τ, max τ gst + δ]`. This file names
the other standard classes of runs of the same model and relates them:

* `Run.SyncValid t δ`: **synchronous** runs, `Run.Valid t δ` with `gst = 0` (every batch between
  correct processes sent at `τ` is delivered in `[τ, τ + δ]`). This is the class used by CSLib's
  `SolvesConsensusAuthSync`.
* `Run.AsyncValidBounded t`: runs that are partially synchronous for *some* delay bound,
  `∃ δ, R.Valid t δ` (asynchronous with an unknown GST and an unknown post-GST delay bound;
  in particular every message between correct processes is delivered).
* `Run.AsyncValid t`: **asynchronous** runs with **unbounded** delays: at most `t` faults and
  delivery times `≥` sending times; nothing else. A message between correct processes is still
  delivered (at the finite time `R.dl q τ p`), but the delays need not be bounded by any constant
  after any time.

These are *different* classes: `SyncValid t δ ⊆ Valid t δ ⊆ AsyncValidBounded t ⊆ AsyncValid t`
(`Run.SyncValid.valid`, `Run.Valid.asyncValidBounded`, `Run.AsyncValidBounded.asyncValid`), and
the last inclusion is strict (e.g. `dl q τ p = 2 τ` is in `AsyncValid` but not in
`AsyncValidBounded`). A protocol correct on `AsyncValid t` is correct on `AsyncValidBounded t`
but not conversely, and an impossibility on `AsyncValidBounded t` (or on `Valid t δ`) implies one
on `AsyncValid t`. Papers state their asynchronous results for one of the two; the choice must be
kept.

The quiet runs `Run.quiet F I` are synchronous with any delay bound (`Run.quiet_syncValid`).
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M VI : Type*} {t δ : ℕ} {R : Run P M VI}

namespace Run

/-- **Synchronous runs**: at most `t` faults, `gst = 0`, and every batch between correct
processes sent at `τ` is delivered in `[τ, τ + δ]`. -/
def SyncValid (t δ : ℕ) (R : Run P M VI) : Prop := R.Valid t δ ∧ R.gst = 0

/-- **Asynchronous runs with eventually bounded delays**: the run is partially synchronous for
some (unknown) post-GST delay bound. -/
def AsyncValidBounded (t : ℕ) (R : Run P M VI) : Prop := ∃ δ, R.Valid t δ

/-- **Asynchronous runs with unbounded delays**: at most `t` faults, and every batch between
correct processes is delivered at or after its sending time (at an arbitrary finite time). -/
structure AsyncValid (t : ℕ) (R : Run P M VI) : Prop where
  card_faulty : R.faulty.card ≤ t
  dl_ge : ∀ q τ p, q ∉ R.faulty → p ∉ R.faulty → τ ≤ R.dl q τ p

/-- Unfolding `Run.SyncValid`. -/
theorem syncValid_iff : R.SyncValid t δ ↔ R.Valid t δ ∧ R.gst = 0 := Iff.rfl

/-- Unfolding `Run.AsyncValidBounded`. -/
theorem asyncValidBounded_iff : R.AsyncValidBounded t ↔ ∃ δ, R.Valid t δ := Iff.rfl

/-- Synchronous runs are described without `gst`: the delays are in `[0, δ]`. -/
theorem syncValid_iff_dl_le : R.SyncValid t δ ↔ R.faulty.card ≤ t ∧
    (∀ q τ p, q ∉ R.faulty → p ∉ R.faulty → τ ≤ R.dl q τ p ∧ R.dl q τ p ≤ τ + δ) ∧ R.gst = 0 := by
  constructor
  · rintro ⟨hV, h0⟩
    refine ⟨hV.card_faulty, fun q τ p hq hp => ⟨hV.dl_ge q τ p hq hp, ?_⟩, h0⟩
    have := hV.dl_le q τ p hq hp
    rw [h0, Nat.max_zero] at this
    exact this
  · rintro ⟨hc, hdl, h0⟩
    exact ⟨⟨hc, fun q τ p hq hp => (hdl q τ p hq hp).1,
      fun q τ p hq hp => (hdl q τ p hq hp).2.trans (by omega)⟩, h0⟩

/-- A synchronous run is partially synchronous. -/
theorem SyncValid.valid (h : R.SyncValid t δ) : R.Valid t δ := h.1

/-- A synchronous run has `gst = 0`. -/
theorem SyncValid.gst_eq (h : R.SyncValid t δ) : R.gst = 0 := h.2

/-- A synchronous run for delay bound `δ` is one for every larger delay bound. -/
theorem SyncValid.mono_delta {δ' : ℕ} (h : R.SyncValid t δ) (hδ : δ ≤ δ') : R.SyncValid t δ' :=
  ⟨⟨h.1.card_faulty, h.1.dl_ge, fun q τ p hq hp => (h.1.dl_le q τ p hq hp).trans (by omega)⟩,
    h.2⟩

/-- A partially synchronous run is asynchronous with eventually bounded delays. -/
theorem Valid.asyncValidBounded (h : R.Valid t δ) : R.AsyncValidBounded t := ⟨δ, h⟩

/-- A synchronous run is asynchronous with eventually bounded delays. -/
theorem SyncValid.asyncValidBounded (h : R.SyncValid t δ) : R.AsyncValidBounded t :=
  h.valid.asyncValidBounded

/-- A partially synchronous run is asynchronous. -/
theorem Valid.asyncValid (h : R.Valid t δ) : R.AsyncValid t := ⟨h.card_faulty, h.dl_ge⟩

/-- Eventually bounded delays are in particular delays of an asynchronous run. -/
theorem AsyncValidBounded.asyncValid (h : R.AsyncValidBounded t) : R.AsyncValid t :=
  let ⟨_, hV⟩ := h; hV.asyncValid

/-- A synchronous run is asynchronous. -/
theorem SyncValid.asyncValid (h : R.SyncValid t δ) : R.AsyncValid t := h.valid.asyncValid

/-- The fault bound of an asynchronous run can be raised. -/
theorem AsyncValid.mono {t' : ℕ} (h : R.AsyncValid t) (ht : t ≤ t') : R.AsyncValid t' :=
  ⟨h.card_faulty.trans ht, h.dl_ge⟩

/-- A quiet run is synchronous for every delay bound. -/
theorem quiet_syncValid {F : Finset P} {I : P → VI} (hF : F.card ≤ t) (δ : ℕ) :
    (quiet (M := M) F I).SyncValid t δ :=
  ⟨quiet_valid hF δ, rfl⟩

end Run

end Cslib.Byzantine.PartialSync
