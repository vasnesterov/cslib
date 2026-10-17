/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Map

/-!
# The containment condition is sufficient for synchronous solvability

Following Civit, Gilbert, Guerraoui, Komatovic, Paramonov and Vidigueira [CivitEtAl2024] (§5):
a validity property satisfies the *containment condition* (CC) if some `Γ` maps every input
configuration `c` to a value admissible for every input configuration contained in `c`. Then
`val` is solvable in synchrony whenever interactive consistency is: run interactive consistency
and decide `Γ` of the agreed vector (Algorithm 2 of [CivitEtAl2024]), a zero-message
post-processing (`Algorithm.mapDecide`).

## Main statements

* `ValidityProperty.ContainmentCondition`: Definition 3 of [CivitEtAl2024] (without the
  computability requirement on `Γ`).
* `SolvesConsensusAuthSync.mapDecide_containment`: correctness of Algorithm 2 (Lemma 9 of
  [CivitEtAl2024]).
* `ValidityProperty.ContainmentCondition.solvableAuthSync`,
  `ValidityProperty.ContainmentCondition.solvableSync`: CC and solvable interactive consistency
  give solvability.

## References

* [P. Civit, S. Gilbert, R. Guerraoui, J. Komatovic, A. Paramonov, M. Vidigueira, *All Byzantine
  Agreement Problems Are Expensive*, PODC 2024][CivitEtAl2024]
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P] {t δ : ℕ}
  {val : ValidityProperty P VI VO}

/-- **Containment condition** (Definition 3 of [CivitEtAl2024], without computability): some `Γ`
maps every input configuration `c` to a value admissible for every input configuration `c'`
contained in `c` (`c ⊒ c'`). -/
def ValidityProperty.ContainmentCondition (t : ℕ) (val : ValidityProperty P VI VO) : Prop :=
  ∃ Γ : Config P VI → VO, ∀ c, IsInputConfig t c → ∀ c', IsInputConfig t c' →
    Contains c c' → Γ c ∈ val c'

/-- **Algorithm 2 / Lemma 9** of [CivitEtAl2024]: if `A` solves interactive consistency in
synchrony and `Γ` witnesses the containment condition, then deciding `Γ` of the agreed vector
solves consensus with `val`. -/
theorem SolvesConsensusAuthSync.mapDecide_containment {Au : Auth P M K}
    {A : Algorithm P M S VI (P → VI)} {Γ : Config P VI → VO}
    (hA : SolvesConsensusAuthSync Au t δ A (icValidity P VI))
    (hΓ : ∀ c, IsInputConfig t c → ∀ c', IsInputConfig t c' → Contains c c' → Γ c ∈ val c') :
    SolvesConsensusAuthSync Au t δ (A.mapDecide fun V => Γ fun q => some (V q)) val :=
  hA.mapDecide fun c hc V hV => hΓ _ (by unfold IsInputConfig; simp [Config.procs]) c hc
    (mem_icValidity_iff.mp hV)

/-- **Lemma 9** of [CivitEtAl2024], authenticated model: CC and authenticated-solvable interactive
consistency give authenticated solvability in synchrony. -/
theorem ValidityProperty.ContainmentCondition.solvableAuthSync (hC : val.ContainmentCondition t)
    (hIC : (icValidity P VI).SolvableAuthSync t δ) : val.SolvableAuthSync t δ := by
  obtain ⟨M, S, K, Au, A, hU, hA⟩ := hIC
  obtain ⟨Γ, hΓ⟩ := hC
  exact ⟨M, S, K, Au, _, hU.mapDecide _, hA.mapDecide_containment hΓ⟩

/-- **Lemma 9** of [CivitEtAl2024], unauthenticated model: CC and solvable interactive consistency
give solvability in synchrony. -/
theorem ValidityProperty.ContainmentCondition.solvableSync (hC : val.ContainmentCondition t)
    (hIC : (icValidity P VI).SolvableSync t δ) : val.SolvableSync t δ := by
  obtain ⟨M, S, A, hA⟩ := hIC
  obtain ⟨Γ, hΓ⟩ := hC
  exact ⟨M, S, _, hA.mapDecide_containment hΓ⟩

end Cslib.Byzantine.PartialSync
