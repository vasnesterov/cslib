/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Sync

/-!
# Post-processing decisions and pre-processing proposals

Zero-cost reductions between agreement problems run an algorithm unchanged and only translate
its proposals or its decisions ("run interactive consistency, then decide `Γ` of the agreed
vector"; "propose `c₀ p` for `0` and `c₁ p` for `1`"). This file provides the two operations on
algorithms of the partially synchronous model and transfers everything else — states, messages,
inboxes, decisions, unforgeability, message counts, and solving consensus — along them.

## Main definitions

* `Algorithm.mapDecide A f`: `A`, with every decision `v` replaced by `f v`.
* `Algorithm.comapInput A g`: `A`, where process `p` starts on the proposal `g p v` instead of `v`.
* `Run.mapInput R g`: the run `R` with proposals `g p (R.inp p)`. A run `R` of
  `A.comapInput g` is the run `R.mapInput g` of `A` (`Run.st_comapInput`).

## Main statements

* `Run.st_mapDecide`, `Run.out_mapDecide`, `Run.inbox_mapDecide`, `Run.decides_mapDecide`,
  `Run.authValid_mapDecide`, `Algorithm.Unforging.mapDecide`, `Run.msgsUpTo_mapDecide`, and the
  analogous `…_comapInput` lemmas.
* `SolvesConsensusAuth.mapDecide`, `SolvesConsensusAuthSync.mapDecide`,
  `SolvesConsensus.mapDecide`: post-processing that sends decisions admissible for an input
  configuration to decisions admissible (for another validity property) for the same input
  configuration preserves solving consensus.
* `Run.st_map`: **equivariance**. If an algorithm `A'` is the image of `A` under maps of messages,
  states and inputs (commuting with `init`, `step`, `send`), then in runs with the same faulty set
  and delivery times and mapped inputs and Byzantine messages, the states are the images (e.g. a
  run computed with Boolean values transfers to the same run with real values).
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S VI VI' VO VO' K : Type*}

/-- Post-processing of decisions: `A.mapDecide f` behaves as `A` and decides `f v` whenever `A`
decides `v`. -/
def Algorithm.mapDecide (A : Algorithm P M S VI VO) (f : VO → VO') : Algorithm P M S VI VO' :=
  { A with decide := fun p s => (A.decide p s).map f }

/-- Pre-processing of proposals: in `A.comapInput g`, process `p` with proposal `v` runs `A` with
proposal `g p v`. -/
def Algorithm.comapInput (A : Algorithm P M S VI VO) (g : P → VI' → VI) :
    Algorithm P M S VI' VO :=
  { A with init := fun p v => A.init p (g p v) }

/-- The run `R` with every proposal `v` of process `p` replaced by `g p v`. -/
def Run.mapInput (R : Run P M VI') (g : P → VI' → VI) : Run P M VI :=
  { R with inp := fun p => g p (R.inp p) }

namespace Run

section mapDecide

variable [DecidableEq P] {A : Algorithm P M S VI VO} {f : VO → VO'} (R : Run P M VI)

@[simp] theorem st_mapDecide : R.st (A.mapDecide f) = R.st A := R.st_congr _ rfl rfl rfl

@[simp] theorem out_mapDecide : R.out (A.mapDecide f) = R.out A := R.out_congr _ rfl rfl rfl

@[simp] theorem inbox_mapDecide : R.inbox (A.mapDecide f) = R.inbox A := by
  funext p τ q
  simp only [inbox_eq_flatMap, dlv, out_mapDecide]

theorem decides_mapDecide {p : P} {w : VO'} :
    R.Decides (A.mapDecide f) p w ↔ ∃ v, R.Decides A p v ∧ f v = w := by
  simp only [Decides, st_mapDecide]
  simp only [Algorithm.mapDecide, Option.map_eq_some_iff]
  exact ⟨fun ⟨τ, v, h, hv⟩ => ⟨v, ⟨τ, h⟩, hv⟩, fun ⟨v, ⟨τ, h⟩, hv⟩ => ⟨τ, v, h, hv⟩⟩

theorem Decides.mapDecide {p : P} {v : VO} (h : R.Decides A p v) :
    R.Decides (A.mapDecide f) p (f v) :=
  (R.decides_mapDecide).2 ⟨v, h, rfl⟩

@[simp] theorem authValid_mapDecide (Au : Auth P M K) :
    R.AuthValid Au (A.mapDecide f) ↔ R.AuthValid Au A := by
  simp only [AuthValid, honestTokens, out_mapDecide]

@[simp] theorem msgsUpTo_mapDecide [Fintype P] (N : ℕ) :
    R.msgsUpTo (A.mapDecide f) N = R.msgsUpTo A N := by
  simp only [msgsUpTo, msgsAt, out_mapDecide]

@[simp] theorem msgComplexity_mapDecide [Fintype P] :
    R.msgComplexity (A.mapDecide f) = R.msgComplexity A := by
  simp only [msgComplexity, msgsUpTo_mapDecide]

end mapDecide

section comapInput

variable {A : Algorithm P M S VI VO} {g : P → VI' → VI} (R : Run P M VI')

@[simp] theorem mapInput_faulty : (R.mapInput g).faulty = R.faulty := rfl
@[simp] theorem mapInput_inp : (R.mapInput g).inp = fun p => g p (R.inp p) := rfl
@[simp] theorem mapInput_gst : (R.mapInput g).gst = R.gst := rfl
@[simp] theorem mapInput_byz : (R.mapInput g).byz = R.byz := rfl
@[simp] theorem mapInput_dl : (R.mapInput g).dl = R.dl := rfl

@[simp] theorem valid_mapInput {t δ : ℕ} : (R.mapInput g).Valid t δ ↔ R.Valid t δ :=
  ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

variable [DecidableEq P]

/-- A run of `A.comapInput g` is the run `R.mapInput g` of `A`. -/
theorem st_comapInput : R.st (A.comapInput g) = (R.mapInput g).st A := by
  funext τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    funext p
    rcases τ with _ | τ
    · rfl
    · rw [st_succ, st_succ, ih τ (by omega)]
      change A.step p _ _ = A.step p _ _
      congr 1
      funext q
      rw [inbox_eq_flatMap, inbox_eq_flatMap]
      refine List.flatMap_congr fun σ hσ => ?_
      have hσ' : σ < τ + 1 := by simpa using hσ
      simp only [dlv]
      congr 1
      by_cases hq : q ∈ R.faulty
      · rw [out_of_faulty _ _ hq, out_of_faulty _ _ (by exact hq)]; rfl
      · rw [out_of_correct _ _ hq, out_of_correct _ _ (by exact hq), ih σ hσ']; rfl

theorem out_comapInput : R.out (A.comapInput g) = (R.mapInput g).out A := by
  funext q τ p
  by_cases hq : q ∈ R.faulty
  · rw [out_of_faulty _ _ hq, out_of_faulty _ _ (by exact hq)]; rfl
  · rw [out_of_correct _ _ hq, out_of_correct _ _ (by exact hq), st_comapInput]; rfl

theorem inbox_comapInput : R.inbox (A.comapInput g) = (R.mapInput g).inbox A := by
  funext p τ q
  simp only [inbox_eq_flatMap, dlv, out_comapInput]
  rfl

theorem decides_comapInput {p : P} {v : VO} :
    R.Decides (A.comapInput g) p v ↔ (R.mapInput g).Decides A p v := by
  simp only [Decides, st_comapInput]
  rfl

theorem authValid_comapInput (Au : Auth P M K) :
    R.AuthValid Au (A.comapInput g) ↔ (R.mapInput g).AuthValid Au A := by
  simp only [AuthValid, honestTokens, out_comapInput]
  rfl

theorem msgsUpTo_comapInput [Fintype P] (N : ℕ) :
    R.msgsUpTo (A.comapInput g) N = (R.mapInput g).msgsUpTo A N := by
  simp only [msgsUpTo, msgsAt, out_comapInput]
  rfl

end comapInput

end Run

section Unforging

variable [DecidableEq P] {A : Algorithm P M S VI VO} {Au : Auth P M K}

theorem Algorithm.Unforging.mapDecide (hU : A.Unforging Au) (f : VO → VO') :
    (A.mapDecide f).Unforging Au := by
  intro R p τ q m hm x hx
  rw [Run.st_mapDecide] at hm
  simpa only [Run.recvTokens, Run.inbox_mapDecide] using hU R p τ q m hm x hx

theorem Algorithm.Unforging.comapInput (hU : A.Unforging Au) (g : P → VI' → VI) :
    (A.comapInput g).Unforging Au := by
  intro R p τ q m hm x hx
  rw [Run.st_comapInput] at hm
  simpa only [Run.recvTokens, Run.inbox_comapInput] using hU (R.mapInput g) p τ q m hm x hx

end Unforging

/-! ### Solving consensus is preserved by admissible post-processing -/

section Solves

variable [Fintype P] [DecidableEq P] {t δ : ℕ} {A : Algorithm P M S VI VO} {f : VO → VO'}
  {val : ValidityProperty P VI VO} {val' : ValidityProperty P VI VO'} {Au : Auth P M K}

/-- If `f` maps decisions admissible for `val` to decisions admissible for `val'` (for every input
configuration), then `A.mapDecide f` solves consensus with `val'` whenever `A` solves it with
`val` (partially synchronous, authenticated model). -/
theorem SolvesConsensusAuth.mapDecide (hA : SolvesConsensusAuth Au t δ A val)
    (hf : ∀ c, IsInputConfig t c → ∀ v ∈ val c, f v ∈ val' c) :
    SolvesConsensusAuth Au t δ (A.mapDecide f) val' where
  termination R hR hRa p hp := by
    obtain ⟨v, hv⟩ := hA.termination R hR ((R.authValid_mapDecide Au).1 hRa) p hp
    exact ⟨f v, hv.mapDecide R⟩
  agreement R hR hRa p hp q hq v w hv hw := by
    obtain ⟨v', hv', rfl⟩ := (R.decides_mapDecide).1 hv
    obtain ⟨w', hw', rfl⟩ := (R.decides_mapDecide).1 hw
    rw [hA.agreement R hR ((R.authValid_mapDecide Au).1 hRa) p hp q hq v' w' hv' hw']
  validity R hR hRa p hp w hw := by
    obtain ⟨v, hv, rfl⟩ := (R.decides_mapDecide).1 hw
    exact hf _ (Run.isInputConfig_inputConf hR) v
      (hA.validity R hR ((R.authValid_mapDecide Au).1 hRa) p hp v hv)

/-- Synchronous version of `SolvesConsensusAuth.mapDecide`. -/
theorem SolvesConsensusAuthSync.mapDecide (hA : SolvesConsensusAuthSync Au t δ A val)
    (hf : ∀ c, IsInputConfig t c → ∀ v ∈ val c, f v ∈ val' c) :
    SolvesConsensusAuthSync Au t δ (A.mapDecide f) val' where
  termination R hR hRa h0 p hp := by
    obtain ⟨v, hv⟩ := hA.termination R hR ((R.authValid_mapDecide Au).1 hRa) h0 p hp
    exact ⟨f v, hv.mapDecide R⟩
  agreement R hR hRa h0 p hp q hq v w hv hw := by
    obtain ⟨v', hv', rfl⟩ := (R.decides_mapDecide).1 hv
    obtain ⟨w', hw', rfl⟩ := (R.decides_mapDecide).1 hw
    rw [hA.agreement R hR ((R.authValid_mapDecide Au).1 hRa) h0 p hp q hq v' w' hv' hw']
  validity R hR hRa h0 p hp w hw := by
    obtain ⟨v, hv, rfl⟩ := (R.decides_mapDecide).1 hw
    exact hf _ (Run.isInputConfig_inputConf hR) v
      (hA.validity R hR ((R.authValid_mapDecide Au).1 hRa) h0 p hp v hv)

/-- Unauthenticated, partially synchronous version of `SolvesConsensusAuth.mapDecide`. -/
theorem SolvesConsensus.mapDecide (hA : SolvesConsensus t δ A val)
    (hf : ∀ c, IsInputConfig t c → ∀ v ∈ val c, f v ∈ val' c) :
    SolvesConsensus t δ (A.mapDecide f) val' :=
  ((hA.auth (Auth.none P M)).mapDecide hf).of_none

end Solves

section Equivariance

variable {M' S' : Type*} [DecidableEq P]

/-- **Equivariance of runs** under maps of messages, states and inputs. -/
theorem Run.st_map {A : Algorithm P M S VI VO} {A' : Algorithm P M' S' VI' VO'}
    (fm : M → M') (fs : S → S') (fi : VI → VI')
    (hinit : ∀ p v, A'.init p (fi v) = fs (A.init p v))
    (hstep : ∀ p s ib, A'.step p (fs s) (fun q => (ib q).map fm) = fs (A.step p s ib))
    (hsend : ∀ p s q, A'.send p (fs s) q = (A.send p s q).map fm)
    {R : Run P M VI} {R' : Run P M' VI'} (hf : R'.faulty = R.faulty)
    (hi : ∀ p, R'.inp p = fi (R.inp p)) (hb : ∀ q τ p, R'.byz q τ p = (R.byz q τ p).map fm)
    (hdl : R'.dl = R.dl) : ∀ τ p, R'.st A' τ p = fs (R.st A τ p) := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro p
    rcases τ with _ | τ
    · simp [hi, hinit]
    · rw [Run.st_succ, Run.st_succ, ih τ (by omega)]
      have hout : ∀ σ ≤ τ, ∀ q r, R'.out A' q σ r = (R.out A q σ r).map fm := by
        intro σ hσ q r
        by_cases hq : q ∈ R.faulty
        · rw [Run.out_of_faulty _ _ (hf ▸ hq), Run.out_of_faulty _ _ hq, hb]
        · rw [Run.out_of_correct _ _ (hf ▸ hq), Run.out_of_correct _ _ hq, ih σ (by omega), hsend]
      have hin : R'.inbox A' p τ = fun q => (R.inbox A p τ q).map fm := by
        funext q
        rw [Run.inbox_eq_flatMap, Run.inbox_eq_flatMap, List.map_flatMap]
        refine List.flatMap_congr fun σ hσ => ?_
        simp only [List.mem_range] at hσ
        simp only [Run.dlv, hdl]
        split_ifs
        · exact hout σ (by omega) q p
        · rfl
      rw [hin, hstep]

end Equivariance

end Cslib.Byzantine.PartialSync
