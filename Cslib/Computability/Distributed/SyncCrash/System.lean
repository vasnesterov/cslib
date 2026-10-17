/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.SyncCrash.Model
public import Cslib.Computability.Distributed.DynamicNetworks.Journey
public import Cslib.Computability.Distributed.Knowledge.Basic

/-!
# The synchronous crash model as an interpreted system

CSLib's synchronous crash model `γ_f` (`Cslib.SyncCrash`) has its own message chains (`Chain`)
and knowledge operator (`Knows`, with knowledge of preconditions `kop`). This file shows that they
are instances of the generic notions of dynamic networks and interpreted systems:

* `chain_iff_journey`: message chains are journeys (`Cslib.DynNet.Journey`) in the dynamic network
  of sent messages (`Sent alg r y z t`: a message from `y` to `z` in round `t + 1`);
* `system alg f`: the interpreted system `R(alg, γ_f)` (admissible runs; the local state of `p` at
  time `m` is the time and `p`'s state, so that processes know the global time; the nonfaulty
  processes are the correct ones), and `knows_iff_K`: `Knows` is its knowledge modality
  (`Cslib.Knowledge.System.K`); `kop_of_isLocal` re-derives `SyncCrash.kop` (for admissible runs)
  from the generic knowledge-of-preconditions principle.
-/

@[expose] public section

namespace Cslib.SyncCrash

open Cslib.DynNet Cslib.Knowledge

variable {P I M O : Type*} {alg : Cslib.Byzantine.LockStep.Protocol P I M O}

/-- **Message chains are journeys** in the dynamic network of sent messages. -/
theorem chain_iff_journey {r : Run P I} {i z : P} {m m' : ℕ} :
    Chain alg r i m z m' ↔ Journey (fun t y z => Sent alg r y z t) m i m' z := by
  constructor
  · intro h
    induction h with
    | refl h => exact Journey.self h
    | snoc _ hs hle ih => exact (Journey.step ih (Or.inr hs)).mono_right hle
  · intro h
    induction h with
    | refl => exact .refl le_rfl
    | step _ hyz ih =>
      rcases hyz with rfl | hs
      · exact ih.trans_le (Nat.le_succ _)
      · exact ih.step hs

variable (alg) in
/-- The interpreted system `R(alg, γ_f)` of the admissible runs of `alg`: the local state of `p` at
time `m` is `(m, state alg r p m)`, the nonfaulty processes are the correct ones. -/
noncomputable def system [Fintype P] (f : ℕ) :
    System P {r : Run P I // r.Admissible f}
      (fun _ => ℕ × Option (I × Cslib.Byzantine.LockStep.History P M)) where
  loc p r m := (m, state alg r.1 p m)
  nf r := {p | ¬ r.1.Faulty p}

/-- **`Knows` is the knowledge modality** of the interpreted system `R(alg, γ_f)`. -/
theorem knows_iff_K [Fintype P] {f : ℕ} {p : P} {m : ℕ} {r : Run P I} (hr : r.Admissible f)
    {φ : Run P I → Prop} :
    Knows alg f p m r φ ↔ (system alg f).K p (RunFact.lift fun r' => φ r'.1) ⟨r, hr⟩ m := by
  rw [System.K_iff]
  constructor
  · rintro h ⟨r', hr'⟩ t' he
    simp only [system, Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    exact h r' hr' he
  · intro h r' hr' he
    exact h ⟨r', hr'⟩ m (by simp [system, he])

/-- Performing an action is local to the performing process. -/
theorem isLocal_performs [Fintype P] (f : ℕ) (p : P)
    (α : I → Cslib.Byzantine.LockStep.History P M → Prop) :
    (system alg f).IsLocal p (fun r m => Performs alg r.1 p m α) := by
  rw [System.isLocal_iff]
  intro r t r' t' h
  simp only [system, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  exact ⟨fun hα => hα.of_state_eq h.symm, fun hα => hα.of_state_eq h⟩

/-- `SyncCrash.kop` (for admissible runs) is an instance of the generic knowledge of
preconditions (`Cslib.Knowledge.IndistSystem.kop_K`). -/
theorem kop_of_isLocal [Fintype P] {f : ℕ} {p : P}
    {α : I → Cslib.Byzantine.LockStep.History P M → Prop} {φ : Run P I → Prop}
    (hnec : ∀ r : Run P I, r.Admissible f → ∀ m, Performs alg r p m α → φ r)
    {r : Run P I} (hr : r.Admissible f) {m : ℕ} (hα : Performs alg r p m α) :
    Knows alg f p m r φ :=
  (knows_iff_K hr).2 <| IndistSystem.kop_K (M := (system alg f).toIndist)
    (α := Function.uncurry fun r m => Performs alg r.1 p m α) (isLocal_performs f p α)
    (fun w hw => hnec w.1.1 w.1.2 w.2 hw) (⟨r, hr⟩, m) hα

end Cslib.SyncCrash
