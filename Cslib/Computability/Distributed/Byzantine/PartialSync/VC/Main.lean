/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.VC.Safety
public import Cslib.Computability.Distributed.Byzantine.PartialSync.VC.Liveness

/-!
# Vector consensus at optimal resilience: main theorem

`VC.solvesVectorConsensus`: for every `t` with `n > 3t`, every `δ`, rounds of length `δ + 1`
and any leader schedule in which every process leads infinitely many views, the compiled
protocol `(VC.algo t leader).compile (δ + 1)` solves vector consensus in the partially
synchronous model (unauthenticated, Byzantine).
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

variable {P M S VI : Type*} [Fintype P] [DecidableEq P]

/-- `A` solves **vector consensus**: Termination, Agreement, and Vector Validity — a decided
vector has exactly `n - t` process-proposal pairs, and the pair of each correct process is its
actual proposal. -/
structure SolvesVectorConsensus (t δ : ℕ) (A : Algorithm P M S VI (Config P VI)) : Prop where
  termination : ∀ R : Run P M VI, R.Valid t δ → ∀ p ∉ R.faulty, ∃ vec, R.Decides A p vec
  agreement : ∀ R : Run P M VI, R.Valid t δ → ∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w,
    R.Decides A p v → R.Decides A q w → v = w
  vectorValidity : ∀ R : Run P M VI, R.Valid t δ → ∀ p ∉ R.faulty, ∀ vec,
    R.Decides A p vec → vec.procs.card = Fintype.card P - t ∧
      ∀ q ∉ R.faulty, vec q ≠ none → vec q = some (R.inp q)

namespace VC

variable {t : ℕ} {leader : ℕ → P}

/-- **Vector consensus is solvable for `n > 3t`** (partially synchronous, unauthenticated,
Byzantine). -/
theorem solvesVectorConsensus (hn : 3 * t < Fintype.card P)
    (hlead : ∀ p k₀, ∃ k ≥ k₀, leader k = p) (δ : ℕ) :
    SolvesVectorConsensus t δ ((algo (VI := VI) t leader).compile (δ + 1)) where
  termination R hR p hp := by
    set E := R.toRoundRun (algo (VI := VI) t leader) (δ + 1) (by omega)
    have hs := R.toRoundRun_syncFrom (RA := algo (VI := VI) t leader) hR (le_refl (δ + 1))
    set r₀ := (R.gst + (δ + 1) - 1) / (δ + 1)
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ ∉ R.faulty := by
      by_contra h
      push Not at h
      have : R.faulty = Finset.univ := Finset.eq_univ_of_forall h
      have := hR.card_faulty
      simp_all
    obtain ⟨k, hk, hkℓ⟩ := hlead ℓ r₀
    have hsync : E.SyncFrom (5 * k) := fun r hr' => hs r (by omega)
    obtain ⟨m, hm⟩ := decides_after_good_view E hn hR.card_faulty hsync (hkℓ ▸ hℓ) p hp
    exact ⟨m, (R.decides_compile_iff (by omega)).mpr ⟨_, hm⟩⟩
  agreement R hR p _ q _ v w hv hw := by
    obtain ⟨r₁, h₁⟩ := (R.decides_compile_iff (by omega)).mp hv
    obtain ⟨r₂, h₂⟩ := (R.decides_compile_iff (by omega)).mp hw
    exact VC.agreement _ hn hR.card_faulty h₁ h₂
  vectorValidity R hR p _ vec hv := by
    obtain ⟨r, h⟩ := (R.decides_compile_iff (by omega)).mp hv
    exact dec_valid _ hn hR.card_faulty h

end VC

end Cslib.Byzantine.PartialSync
