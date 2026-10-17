/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.RoundOne
public import Cslib.Computability.Distributed.Byzantine.PartialSync.Sync

/-!
# Quiet runs and decision deadlines

Complements `Cslib.Byzantine.PartialSync.Constructions`.

* `Run.quiet F I`: the synchronous run (`gst = 0`, every batch delivered at once) in which the
  processes of `F` are faulty and silent and the proposals are `I`. The standard runs of CSLib
  are instances: `canonRun c d` (`F = π(c)ᶜ`), `isoRun Q v` (`F = {Q}ᶜ`) and `silentRun v`
  (`F = univ`); `quiet ∅ I` is the fault-free lock-step run.
* `Run.DecidesBy A R p v T`: `p` decides `v` at some time `≤ T` (`Run.Decides` with a deadline),
  with `DecidesBy.decides`, `DecidesBy.mono` and `decides_iff_exists_decidesBy`.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S VI VO K : Type*}

/-! ### Quiet runs -/

/-- The synchronous run with zero delays in which the processes of `F` are faulty and silent and
the proposals are `I`. -/
def Run.quiet (F : Finset P) (I : P → VI) : Run P M VI where
  faulty := F
  inp := I
  gst := 0
  byz _ _ _ := []
  dl _ τ _ := τ

namespace Run

variable {F : Finset P} {I : P → VI}

@[simp] theorem quiet_faulty : (quiet (M := M) F I).faulty = F := rfl
@[simp] theorem quiet_inp : (quiet (M := M) F I).inp = I := rfl
@[simp] theorem quiet_gst : (quiet (M := M) F I).gst = 0 := rfl
@[simp] theorem quiet_byz : (quiet (M := M) F I).byz = fun _ _ _ => [] := rfl
@[simp] theorem quiet_dl : (quiet (M := M) F I).dl = fun _ τ _ => τ := rfl

theorem quiet_valid {t : ℕ} (hF : F.card ≤ t) (δ : ℕ) : (quiet (M := M) F I).Valid t δ :=
  ⟨hF, fun _ _ _ _ _ => le_rfl, fun _ τ _ _ _ => by simp⟩

theorem quiet_canonical : (quiet (M := M) F I).Canonical := fun _ _ _ _ => rfl

theorem quiet_authValid [DecidableEq P] {Au : Auth P M K} {A : Algorithm P M S VI VO} :
    (quiet (M := M) F I).AuthValid Au A :=
  authValid_of_canonical quiet_canonical

/-- In a quiet run, `p` receives at time `τ` exactly what the correct processes send it at `τ`. -/
theorem quiet_inbox [DecidableEq P] (A : Algorithm P M S VI VO) (p : P) (τ : ℕ) (q : P) :
    (quiet (M := M) F I).inbox A p τ q =
      if q ∈ F then [] else A.send q ((quiet F I).st A τ q) p := by
  rw [inbox_of_dl_eq A (fun _ _ _ => rfl)]
  split_ifs with hq
  · exact out_eq_nil_of_canonical A quiet_canonical hq τ p
  · exact out_of_correct A _ hq τ p

end Run

section Instances

variable [Fintype P] [DecidableEq P]

/-- The canonical run of a configuration is a quiet run. -/
theorem canonRun_eq_quiet (c : Config P VI) (d : VI) :
    canonRun (M := M) c d = Run.quiet c.procsᶜ fun p => (c p).getD d := rfl

/-- The run of `Q` in isolation is a quiet run. -/
theorem isoRun_eq_quiet (Q : P) (v : VI) : isoRun (M := M) Q v = Run.quiet {Q}ᶜ fun _ => v := rfl

omit [DecidableEq P] in
/-- The run in which everybody is faulty and silent is a quiet run. -/
theorem silentRun_eq_quiet (v : VI) : silentRun (M := M) (P := P) v = Run.quiet univ fun _ => v :=
  rfl

end Instances

/-! ### Deciding by a deadline -/

namespace Run

variable [DecidableEq P] (A : Algorithm P M S VI VO) (R : Run P M VI)

/-- `p` decides `v` at some time `≤ T`. -/
def DecidesBy (p : P) (v : VO) (T : ℕ) : Prop := ∃ τ ≤ T, A.decide p (R.st A τ p) = some v

variable {A R} {p : P} {v : VO} {T T' : ℕ}

theorem DecidesBy.decides (h : R.DecidesBy A p v T) : R.Decides A p v :=
  let ⟨τ, _, hτ⟩ := h; ⟨τ, hτ⟩

theorem DecidesBy.mono (h : R.DecidesBy A p v T) (hT : T ≤ T') : R.DecidesBy A p v T' :=
  let ⟨τ, hτ, hd⟩ := h; ⟨τ, hτ.trans hT, hd⟩

theorem decides_iff_exists_decidesBy : R.Decides A p v ↔ ∃ T, R.DecidesBy A p v T :=
  ⟨fun ⟨τ, hτ⟩ => ⟨τ, τ, le_rfl, hτ⟩, fun ⟨_, h⟩ => h.decides⟩

end Run

end Cslib.Byzantine.PartialSync
