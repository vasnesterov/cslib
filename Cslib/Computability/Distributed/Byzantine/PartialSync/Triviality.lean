/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Merge

/-!
# Byzantine consensus with `n ≤ 3t` only solves trivial validity properties

Following Civit, Gilbert, Guerraoui, Komatovic and Vidigueira [CivitEtAl2023] (§3.4, §4.1): if
`n ≤ 3t`, every validity property with which some algorithm solves Byzantine consensus in the
partially synchronous model is *trivial*: some decision is admissible for every input
configuration. All results hold in the authenticated model (ideal signatures, unforging
algorithms); the unauthenticated model is the special case `Auth.none`.

## Main statements

* `SolvesConsensusAuth.mem_of_similar` (canonical similarity, Lemma 1 of [CivitEtAl2023]): a value
  decided in a canonical execution corresponding to `c` is admissible for every input
  configuration similar to `c`.
* `SolvesConsensusAuth.eq_of_compatible` (merging, Lemma 2 of [CivitEtAl2023]): canonical
  executions with compatible input configurations decide the same value (via `Run.merge`).
* `SolvesConsensusAuth.trivial`, `ValidityProperty.SolvableAuth.trivial`,
  `ValidityProperty.Solvable.trivial` (Theorem 1 of [CivitEtAl2023]): if `0 < t < n ≤ 3t`, every
  solvable validity property is trivial.

## References

* [P. Civit, S. Gilbert, R. Guerraoui, J. Komatovic, M. Vidigueira, *On the Validity of
  Consensus*, PODC 2023][CivitEtAl2023]
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P] {t δ : ℕ}
  {A : Algorithm P M S VI VO} {val : ValidityProperty P VI VO} {Au : Auth P M K}

/-- **Lemma 1 (canonical similarity)** of [CivitEtAl2023]. In a canonical execution
corresponding to `c`, a correct process can only decide a value admissible for every input
configuration similar to `c`. -/
theorem SolvesConsensusAuth.mem_of_similar (hA : SolvesConsensusAuth Au t δ A val)
    (hU : A.Unforging Au) {R : Run P M VI} (hR : R.Valid t δ) (hcan : R.Canonical) {p : P}
    (hp : p ∉ R.faulty) {v : VO} (hv : R.Decides A p v) {c' : Config P VI}
    (hc' : IsInputConfig t c') (hsim : Similar c' R.inputConf) : v ∈ val c' := by
  obtain ⟨p', hp'⟩ := hsim.1
  rw [mem_inter, Config.mem_procs_iff_ne_none, Run.mem_procs_inputConf] at hp'
  have hRa : R.AuthValid Au A := Run.authValid_of_canonical hcan
  obtain ⟨w, τ, hw⟩ := hA.termination R hR hRa p' hp'.2
  obtain rfl : w = v := hA.agreement R hR hRa p' hp'.2 p hp w v ⟨τ, hw⟩ hv
  have hagree : ∀ q ∉ R.faulty, c' q ≠ none → c' q = some (R.inp q) := by
    intro q hq hq'
    rw [hsim.2 q (by simp [Option.isSome_iff_ne_none, hq', Run.mem_procs_inputConf.mpr hq])]
    simp [Run.inputConf, hq]
  have hR' := Run.extend_valid (A := A) hR hc' τ
  have hdec : (R.extend A c' τ).Decides A p' w :=
    ⟨τ, by rw [Run.extend_st hcan hagree τ τ le_rfl p' hp'.2 hp'.1]; exact hw⟩
  have := hA.validity _ hR' (Run.extend_authValid hU hcan hagree τ) p'
    (by simp [Run.extend, Option.isSome_iff_ne_none, hp'.1]) w hdec
  rwa [Run.extend_inputConf] at this

/-- **Lemma 2 (merging)** of [CivitEtAl2023]. Two canonical executions with compatible input
configurations decide the same value (the classical partitioning argument): the processes in
`π(c₁) ∩ π(c₂)` (at most `t`) are made Byzantine and behave towards `π(c₁) \ π(c₂)` as in the
first execution and towards `π(c₂) \ π(c₁)` as in the second, while communication between the
two sides is delayed beyond both decisions. -/
theorem SolvesConsensusAuth.eq_of_compatible (hA : SolvesConsensusAuth Au t δ A val)
    (hU : A.Unforging Au) {R₁ R₂ : Run P M VI}
    (h₁ : R₁.Valid t δ) (h₂ : R₂.Valid t δ) (hc₁ : R₁.Canonical) (hc₂ : R₂.Canonical)
    (hcomp : Compatible t R₁.inputConf R₂.inputConf) {p₁ p₂ : P} {v₁ v₂ : VO}
    (hp₁ : p₁ ∉ R₁.faulty) (hd₁ : R₁.Decides A p₁ v₁)
    (hp₂ : p₂ ∉ R₂.faulty) (hd₂ : R₂.Decides A p₂ v₂) : v₁ = v₂ := by
  obtain ⟨a, ha⟩ := hcomp.2.1
  obtain ⟨c, hc⟩ := hcomp.2.2
  simp only [mem_sdiff, Run.mem_procs_inputConf, not_not] at ha hc
  have ha₁ := Run.authValid_of_canonical (Au := Au) (A := A) hc₁
  have ha₂ := Run.authValid_of_canonical (Au := Au) (A := A) hc₂
  obtain ⟨w₁, T₁, hw₁⟩ := hA.termination R₁ h₁ ha₁ a ha.1
  obtain rfl : w₁ = v₁ := hA.agreement R₁ h₁ ha₁ a ha.1 p₁ hp₁ w₁ v₁ ⟨T₁, hw₁⟩ hd₁
  obtain ⟨w₂, T₂, hw₂⟩ := hA.termination R₂ h₂ ha₂ c hc.1
  obtain rfl : w₂ = v₂ := hA.agreement R₂ h₂ ha₂ c hc.1 p₂ hp₂ w₂ v₂ ⟨T₂, hw₂⟩ hd₂
  set T := max T₁ T₂
  -- the merged execution: `π(c₁) ∩ π(c₂)` is Byzantine
  have hcard : (R₁.faultyᶜ ∩ R₂.faultyᶜ).card ≤ t := by
    have := hcomp.1
    rw [Run.procs_inputConf, Run.procs_inputConf, ← filter_and] at this
    convert this using 2
    ext p; simp
  refine hA.agreement (R₁.merge A R₂ T) (Run.merge_valid hcard h₁.dl_ge h₂.dl_ge)
    (Run.merge_authValid hU hc₁ hc₂) a (by simp [ha.2]) c (by simp [hc.2]) w₁ w₂
    (Run.merge_decides_left hc₁ ha.1 ha.2 (le_max_left _ _) hw₁)
    (Run.merge_decides_right hc₂ hc.2 hc.1 (le_max_right _ _) hw₂)

/-- **Lemmas 3, 4 and Theorem 1** of [CivitEtAl2023]: if `0 < t < n ≤ 3t`, any validity property
with which an algorithm solves consensus is trivial. -/
theorem SolvesConsensusAuth.trivial [Nonempty VI] (hA : SolvesConsensusAuth Au t δ A val)
    (hU : A.Unforging Au) (ht : 0 < t) (htn : t < Fintype.card P) (hn : Fintype.card P ≤ 3 * t) :
    val.Trivial t := by
  classical
  set n := Fintype.card P with hn_def
  let d : VI := Classical.arbitrary VI
  obtain ⟨B₀, -, hB₀⟩ := exists_subset_card_eq (s := (univ : Finset P)) (n := n - t)
    (by simp [n])
  let base : Config P VI := fun p => if p ∈ B₀ then some d else none
  have hbase_procs : base.procs = B₀ := by
    ext p; by_cases hp : p ∈ B₀ <;> simp [base, hp]
  let Rb : Run P M VI := canonRun base d
  have hRb : Rb.Valid t δ :=
    canonRun.valid base d (by unfold IsInputConfig; rw [hbase_procs, hB₀]) δ
  obtain ⟨pb, hpb⟩ : B₀.Nonempty := card_pos.mp (by omega)
  have hpbF : pb ∉ Rb.faulty := by simp [Rb, canonRun, hbase_procs, hpb]
  obtain ⟨vb, hvb⟩ := hA.termination Rb hRb (canonRun_authValid _ _) pb hpbF
  -- Lemma 3: for every full input configuration, some execution decides `vb`
  have lemma3 : ∀ cn : Config P VI, (∀ p, cn p ≠ none) → ∃ R : Run P M VI, R.Valid t δ ∧
      R.Canonical ∧ R.inputConf = cn ∧ ∃ p ∉ R.faulty, R.Decides A p vb := by
    intro cn hcn
    obtain ⟨U, hUsub, hUc⟩ := exists_subset_card_eq (s := B₀ᶜ) (n := min t (n - t))
      (by rw [card_compl, hB₀]; omega)
    obtain ⟨Y, hY, hYc⟩ := exists_subset_card_eq (s := B₀) (n := n - t - min t (n - t))
      (by omega)
    have hUY : Disjoint U Y :=
      disjoint_of_subset_left hUsub (disjoint_of_subset_right hY disjoint_compl_left)
    have hUB : ∀ p ∈ U, p ∉ B₀ := fun p hp => by simpa using hUsub hp
    set X := U ∪ Y with hX
    have hXc : X.card = n - t := by rw [card_union_of_disjoint hUY]; omega
    let c : Config P VI := fun p => if p ∈ X then cn p else none
    have hcprocs : c.procs = X := by
      ext p; by_cases hp : p ∈ X <;> simp [c, hp, Option.isSome_iff_ne_none, hcn]
    let Rc : Run P M VI := canonRun c d
    have hc : IsInputConfig t c := by unfold IsInputConfig; rw [hcprocs, hXc]
    have hRc : Rc.Valid t δ := canonRun.valid c d hc δ
    have hXB : X ∩ B₀ ⊆ Y := by
      intro p hp
      rw [mem_inter, hX, mem_union] at hp
      rcases hp.1 with h | h
      · exact absurd hp.2 (hUB p h)
      · exact h
    have hcomp : Compatible t Rc.inputConf Rb.inputConf := by
      rw [canonRun.inputConf, canonRun.inputConf, Compatible, hcprocs, hbase_procs]
      refine ⟨(card_le_card hXB).trans (by omega), ?_, ?_⟩
      · obtain ⟨u, hu⟩ : U.Nonempty := card_pos.mp (by omega)
        exact ⟨u, mem_sdiff.mpr ⟨mem_union_left _ hu, hUB u hu⟩⟩
      · rw [← card_pos]
        have h1 := card_sdiff_add_card_inter B₀ X
        have h2 := card_le_card hXB
        rw [inter_comm] at h1
        omega
    obtain ⟨pc, hpc⟩ : X.Nonempty := card_pos.mp (by omega)
    have hpcF : pc ∉ Rc.faulty := by simp [Rc, canonRun, hcprocs, hpc]
    obtain ⟨vc, τc, hvc⟩ := hA.termination Rc hRc (canonRun_authValid _ _) pc hpcF
    obtain rfl : vc = vb := hA.eq_of_compatible hU hRc hRb (canonRun.canonical c d)
      (canonRun.canonical base d) hcomp hpcF ⟨τc, hvc⟩ hpbF hvb
    have hcn_procs : cn.procs = univ := by
      ext p; simp [Option.isSome_iff_ne_none, hcn]
    have hagree : ∀ p ∉ Rc.faulty, cn p ≠ none → cn p = some (Rc.inp p) := by
      intro p hp _
      have hpX : p ∈ X := by simpa [Rc, canonRun, hcprocs] using hp
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hcn p)
      simp [Rc, canonRun, c, hpX, hv]
    refine ⟨Rc.extend A cn τc,
      Run.extend_valid hRc (by unfold IsInputConfig; rw [hcn_procs, card_univ]; omega) τc,
      fun q hq => by simp [Run.extend, Option.isSome_iff_ne_none, hcn] at hq,
      Run.extend_inputConf _ _ _, pc, by simp [Run.extend, Option.isSome_iff_ne_none, hcn],
      ⟨τc, ?_⟩⟩
    rw [Run.extend_st (canonRun.canonical c d) hagree τc τc le_rfl pc hpcF (hcn pc)]
    exact hvc
  -- Lemma 4: `vb` is admissible for every input configuration
  refine ⟨vb, fun c hc => ?_⟩
  let cn : Config P VI := fun p => if c p = none then some d else c p
  have hcn : ∀ p, cn p ≠ none := by
    intro p; by_cases hp : c p = none <;> simp [cn, hp]
  obtain ⟨R, hR, hcan, hinp, p, hp, hdec⟩ := lemma3 cn hcn
  refine hA.mem_of_similar hU hR hcan hp hdec hc ⟨?_, ?_⟩
  · obtain ⟨q, hq⟩ : c.procs.Nonempty := card_pos.mp (by unfold IsInputConfig at hc; omega)
    refine ⟨q, mem_inter.mpr ⟨hq, ?_⟩⟩
    rw [hinp, Config.mem_procs_iff_ne_none]; exact hcn q
  · intro q hq
    rw [mem_inter, Config.mem_procs_iff_ne_none] at hq
    rw [hinp]; simp [cn, hq.1]

/-- **Theorem 1** of [CivitEtAl2023], authenticated model: if `0 < t < n ≤ 3t`, every validity
property solvable with (ideal) signatures is trivial. -/
theorem ValidityProperty.SolvableAuth.trivial [Nonempty VI] (h : val.SolvableAuth t δ)
    (ht : 0 < t) (htn : t < Fintype.card P) (hn : Fintype.card P ≤ 3 * t) : val.Trivial t := by
  obtain ⟨M, S, K, Au, A, hU, hA⟩ := h
  exact hA.trivial hU ht htn hn

/-- **Theorem 1** of [CivitEtAl2023]: if `0 < t < n ≤ 3t`, every solvable validity property is
trivial. -/
theorem ValidityProperty.Solvable.trivial [Nonempty VI] (h : val.Solvable t δ) (ht : 0 < t)
    (htn : t < Fintype.card P) (hn : Fintype.card P ≤ 3 * t) : val.Trivial t :=
  h.solvableAuth.trivial ht htn hn

end Cslib.Byzantine.PartialSync
