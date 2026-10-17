/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Model

/-!
# Byzantine consensus with a general validity property

Following Civit, Gilbert, Guerraoui, Komatovic and Vidigueira [CivitEtAl2023], a validity property
maps every *input configuration* (an assignment of proposals to the correct processes) to the set of
admissible decisions.

* `Config P VI := P → Option VI`; `c p = none` means that `p` is not in `π(c)` (i.e. faulty).
* `IsInputConfig t c`: `c` assigns proposals to at least `n - t` processes.
* `Run.inputConf R`: the input configuration a run corresponds to (correct processes ↦ proposal).
* `SolvesConsensus t δ A val`: Termination, Agreement and `val`-Validity in every valid run.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S VI VO : Type*} [Fintype P] [DecidableEq P]

/-- A (partial) assignment of proposals to processes. -/
abbrev Config (P VI : Type*) := P → Option VI

namespace Config

/-- `π(c)`: the processes included in `c`. -/
def procs (c : Config P VI) : Finset P := univ.filter fun p => (c p).isSome

omit [DecidableEq P] in
@[simp] theorem mem_procs {c : Config P VI} {p : P} : p ∈ c.procs ↔ (c p).isSome := by
  simp [procs]

omit [DecidableEq P] in
theorem mem_procs_iff_ne_none {c : Config P VI} {p : P} : p ∈ c.procs ↔ c p ≠ none := by
  simp [Option.isSome_iff_ne_none]

end Config

/-- An *input configuration*: proposals for at least `n - t` processes. -/
def IsInputConfig (t : ℕ) (c : Config P VI) : Prop := Fintype.card P - t ≤ c.procs.card

/-- Similarity `c₁ ∼ c₂`: some common process, and common processes have equal proposals. -/
def Similar (c₁ c₂ : Config P VI) : Prop :=
  (c₁.procs ∩ c₂.procs).Nonempty ∧ ∀ p ∈ c₁.procs ∩ c₂.procs, c₁ p = c₂ p

/-- Compatibility `c₁ ⋄ c₂`. -/
def Compatible (t : ℕ) (c₁ c₂ : Config P VI) : Prop :=
  (c₁.procs ∩ c₂.procs).card ≤ t ∧ (c₁.procs \ c₂.procs).Nonempty ∧ (c₂.procs \ c₁.procs).Nonempty

/-- A validity property: admissible decisions for each input configuration (only its values on
input configurations matter). -/
abbrev ValidityProperty (P VI VO : Type*) := Config P VI → Set VO

/-- A validity property is *trivial* if some decision is admissible for every input
configuration. -/
def ValidityProperty.Trivial (t : ℕ) (val : ValidityProperty P VI VO) : Prop :=
  ∃ v, ∀ c : Config P VI, IsInputConfig t c → v ∈ val c

namespace Run

/-- The input configuration a run corresponds to. -/
def inputConf (R : Run P M VI) : Config P VI :=
  fun p => if p ∈ R.faulty then none else some (R.inp p)

theorem procs_inputConf (R : Run P M VI) : R.inputConf.procs = univ.filter (· ∉ R.faulty) := by
  ext p; by_cases hp : p ∈ R.faulty <;> simp [inputConf, hp]

theorem mem_procs_inputConf {R : Run P M VI} {p : P} : p ∈ R.inputConf.procs ↔ p ∉ R.faulty := by
  simp [procs_inputConf]

theorem isInputConfig_inputConf {t δ : ℕ} {R : Run P M VI} (hR : R.Valid t δ) :
    IsInputConfig t R.inputConf := by
  have h1 : (univ.filter (· ∉ R.faulty)).card = Fintype.card P - R.faulty.card := by
    rw [filter_not, card_sdiff_of_subset (by simp)]; simp
  rw [IsInputConfig, procs_inputConf, h1]
  have := hR.card_faulty
  omega

end Run

/-- `A` solves Byzantine consensus with validity property `val` (with at most `t` faults and
post-GST delay bound `δ`). Agreement is quantified over all pairs of correct processes,
including `p = q`, so a correct process cannot "change its mind". -/
structure SolvesConsensus (t δ : ℕ) (A : Algorithm P M S VI VO)
    (val : ValidityProperty P VI VO) : Prop where
  termination : ∀ R : Run P M VI, R.Valid t δ → ∀ p ∉ R.faulty, ∃ v, R.Decides A p v
  agreement : ∀ R : Run P M VI, R.Valid t δ → ∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w,
    R.Decides A p v → R.Decides A q w → v = w
  validity : ∀ R : Run P M VI, R.Valid t δ → ∀ p ∉ R.faulty, ∀ v,
    R.Decides A p v → v ∈ val R.inputConf

/-- A validity property is *solvable* if some algorithm solves consensus with it. -/
def ValidityProperty.Solvable (t δ : ℕ) (val : ValidityProperty P VI VO) : Prop :=
  ∃ (M S : Type) (A : Algorithm P M S VI VO), SolvesConsensus t δ A val

end Cslib.Byzantine.PartialSync
