/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.LockStep.Basic
public import Cslib.Computability.Distributed.Byzantine.PartialSync.Model

/-!
# Lock-step protocols as partially synchronous algorithms

This file relates the two Byzantine message-passing models of CSLib:

* the synchronous lock-step model `Cslib.Byzantine.LockStep` (history-based protocols on a
  communication graph, adversary = a `Scenario`), and
* the partially synchronous model `Cslib.Byzantine.PartialSync` (state machines on a complete
  network, adversary = a `Run` with delivery times and a global stabilization time).

A lock-step protocol `alg` on a network `G` is compiled into a partially synchronous algorithm
`alg.toAlgorithm G` whose state is the input together with the history of received inboxes; at
every time step a process appends to its history, for each neighbour, the first message received
from it. In runs with `gst = 0` and `δ = 0` (the lock-step special case of the partially
synchronous model), the state of every correct process at time `r` is exactly its input and its
lock-step history after `r` rounds in the scenario `R.toScenario` induced by the run
(`toAlgorithm_st`). Consequently lock-step decisions are decisions in the partially synchronous
run (`Run.decides_toAlgorithm_of_decides`), and lock-step correctness transfers
(`Solves.toAlgorithm`).

## Main definitions

* `Protocol.toAlgorithm G alg`: the compiled algorithm.
* `Cslib.Byzantine.PartialSync.Run.toScenario R`: the lock-step scenario of a run (same faulty
  set and inputs; a faulty process sends, in round `r`, the first message of the batches it has
  delivered at time `r`).

## Main results

* `toAlgorithm_st`: the simulation lemma.
* `Solves.toAlgorithm`: if `alg` solves `spec` on `G`, then in every valid lock-step run of the
  compiled algorithm whose faulty set is admissible, the decisions satisfy `spec`.
-/

@[expose] public section

namespace Cslib.Byzantine

variable {P I M O : Type*}

/-- The lock-step scenario induced by a partially synchronous run: same faulty processes and
inputs, no omissions, and a faulty `q` sends to `p` in round `r` the first message of the batches
from `q` that are delivered to `p` at time `r`. -/
def PartialSync.Run.toScenario (R : PartialSync.Run P M I) : LockStep.Scenario P I M where
  byz := ↑R.faulty
  input := R.inp
  adv r q p :=
    ((List.range (r + 1)).flatMap fun τ' => if R.dl q τ' p = r then R.byz q τ' p else []).head?

namespace LockStep

open Classical in
/-- Compile a lock-step protocol on the network `G` into the partially synchronous model. The
local state is the input together with the lock-step history; at every step, a process appends
the inbox made of the first message received from each neighbour. Messages are only sent to
neighbours. -/
noncomputable def Protocol.toAlgorithm (G : SimpleGraph P) (alg : Protocol P I M O) :
    PartialSync.Algorithm P M (I × History P M) I O where
  init _ x := (x, [])
  step p s inbox := (s.1, s.2 ++ [fun q => if G.Adj q p then (inbox q).head? else none])
  send p s q := if G.Adj p q then (alg.send p s.1 s.2 q).toList else []
  decide p s := alg.decide p s.1 s.2

variable (G : SimpleGraph P) (alg : Protocol P I M O)

open Classical in
@[simp] lemma toAlgorithm_step (p : P) (s : I × History P M) (inbox : P → List M) :
    (alg.toAlgorithm G).step p s inbox =
      (s.1, s.2 ++ [fun q => if G.Adj q p then (inbox q).head? else none]) := rfl

open Classical in
@[simp] lemma toAlgorithm_send (p : P) (s : I × History P M) (q : P) :
    (alg.toAlgorithm G).send p s q = if G.Adj p q then (alg.send p s.1 s.2 q).toList else [] :=
  rfl

/-- **Transfer of correctness.** If `alg` solves `spec` on `G` against the adversary structure
`Z`, then every valid lock-step run (`gst = 0`, `δ = 0`) of the compiled algorithm with an
admissible faulty set satisfies `spec` for the first decisions of the induced scenario, which are
decisions of the run by `PartialSync.Run.decides_toAlgorithm_of_decides`. -/
theorem Solves.toAlgorithm {Z : AdvStructure P} {spec : Spec P I O} (h : Solves G alg Z spec)
    (R : PartialSync.Run P M I) (hZ : (↑R.faulty : Set P) ∈ Z) :
    spec R.inp (↑R.faulty : Set P)ᶜ (Decides G alg R.toScenario) :=
  h R.toScenario hZ fun _ _ _ h => h

variable [DecidableEq P]

lemma flatMap_range_ite_eq {α : Type*} (r : ℕ) (f : ℕ → List α) :
    ((List.range (r + 1)).flatMap fun τ' => if τ' = r then f τ' else []) = f r := by
  rw [List.range_succ, List.flatMap_append]
  have : ((List.range r).flatMap fun τ' => if τ' = r then f τ' else []) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro τ' hτ'
    rw [ite_eq_right_iff]
    intro h
    simp at hτ'
    omega
  simp [this]

/-- **Simulation lemma.** In a run of the compiled algorithm with `gst = 0` and `δ = 0`, every
correct process has, at time `r`, its input and its lock-step history after `r` rounds in the
induced scenario. -/
theorem toAlgorithm_st {R : PartialSync.Run P M I} {t : ℕ} (hR : R.Valid t 0) (h0 : R.gst = 0) :
    ∀ r, ∀ p ∉ R.faulty,
      R.st (alg.toAlgorithm G) r p = (R.inp p, hist G alg R.toScenario r p) := by
  intro r
  induction r with
  | zero => intro p _; rfl
  | succ r ih =>
    intro p hp
    rw [PartialSync.Run.st_succ, ih p hp, hist_succ]
    simp only [toAlgorithm_step, Prod.mk.injEq, true_and]
    congr 1
    refine congrArg (fun f => [f]) (funext fun q => ?_)
    simp only [deliver]
    by_cases hadj : G.Adj q p
    · simp only [hadj, ite_true]
      by_cases hq : q ∈ R.faulty
      · simp [PartialSync.Run.inbox, PartialSync.Run.inboxWith, PartialSync.Run.outWith, hq,
          PartialSync.Run.toScenario]
      · have hdl : ∀ τ', R.dl q τ' p = τ' := fun τ' =>
          le_antisymm (by simpa [h0] using hR.dl_le q τ' p hq hp) (hR.dl_ge q τ' p hq hp)
        rw [PartialSync.Run.inbox_eq_flatMap]
        simp only [PartialSync.Run.dlv, hdl]
        rw [flatMap_range_ite_eq r (fun τ' => R.out (alg.toAlgorithm G) q τ' p),
          PartialSync.Run.out_of_correct _ _ hq, ih q hq]
        have hq' : q ∉ R.toScenario.byz := by simpa [PartialSync.Run.toScenario] using hq
        simp only [hq', ↓reduceIte]
        simp [hadj, PartialSync.Run.toScenario]
    · simp [hadj]

/-- Lock-step decisions of correct processes are decisions in the partially synchronous run. -/
theorem _root_.Cslib.Byzantine.PartialSync.Run.decides_toAlgorithm_of_decides
    {R : PartialSync.Run P M I} {t : ℕ} (hR : R.Valid t 0) (h0 : R.gst = 0) {p : P}
    (hp : p ∉ R.faulty) {o : O} (h : Decides G alg R.toScenario p o) :
    R.Decides (alg.toAlgorithm G) p o := by
  obtain ⟨r, hr, -⟩ := h
  exact ⟨r, by rw [toAlgorithm_st G alg hR h0 r p hp]; exact hr⟩


end LockStep

end Cslib.Byzantine
