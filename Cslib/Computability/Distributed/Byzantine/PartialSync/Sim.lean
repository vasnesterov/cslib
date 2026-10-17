/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Sync

/-!
# Memoised simulation of concrete runs

`Run.st` recomputes the whole history at every step, so evaluating it on a concrete run is
exponential in the time. For runs on `Fin n` the global states can instead be computed once per
tick, which the kernel evaluates quickly; facts about a concrete finite run prefix can then be
checked by `decide`.

* `simHist A inp bad byz dl d τ`: the list of the global states at times `0, …, τ` of the run with
  inputs `inp`, faulty set `bad`, Byzantine messages `byz` and delivery times `dl` (`d` is a dummy
  state for out-of-range indices); `Run.st_eq_simHist` identifies it with `Run.st`.
* `simStates A inp bad byz d τ`: the global state at time `τ` of a run with zero delays
  (`dl q τ p = τ`), computed without keeping the history; `Run.st_eq_simStates`. This is the
  cheaper special case for zero-delay runs.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

variable {n : ℕ} {M S VI VO : Type*}

/-- Reading a list built by `List.ofFn` at an index of `Fin n`. -/
theorem _root_.List.getD_ofFn {α : Type*} (f : Fin n → α) (p : Fin n) (d : α) :
    (List.ofFn f).getD p d = f p := by
  simp [List.getD_eq_getElem?_getD]

/-! ### Arbitrary delays -/

/-- The global state at time `τ + 1`, given the history `hist` of global states at times `0..τ`. -/
def simNext (A : Algorithm (Fin n) M S VI VO) (bad : Fin n → Bool)
    (byz : Fin n → ℕ → Fin n → List M) (dl : Fin n → ℕ → Fin n → ℕ) (d : S)
    (hist : List (List S)) (τ : ℕ) : List S :=
  List.ofFn fun p => A.step p ((hist.getD τ []).getD p d) fun q =>
    (List.range (τ + 1)).flatMap fun τ' =>
      if dl q τ' p = τ then
        (if bad q then byz q τ' p else A.send q ((hist.getD τ' []).getD q d) p)
      else []

/-- Memoised history of global states at times `0..τ` (`d` is a dummy state). -/
def simHist (A : Algorithm (Fin n) M S VI VO) (inp : Fin n → VI) (bad : Fin n → Bool)
    (byz : Fin n → ℕ → Fin n → List M) (dl : Fin n → ℕ → Fin n → ℕ) (d : S) :
    ℕ → List (List S)
  | 0 => [List.ofFn fun p => A.init p (inp p)]
  | τ + 1 =>
    let h := simHist A inp bad byz dl d τ
    h ++ [simNext A bad byz dl d h τ]

section simHist

variable (A : Algorithm (Fin n) M S VI VO) (inp : Fin n → VI) (bad : Fin n → Bool)
  (byz : Fin n → ℕ → Fin n → List M) (dl : Fin n → ℕ → Fin n → ℕ) (d : S)

/-- `simHist … τ` lists the global states at times `0, …, τ`. -/
@[simp] theorem simHist_length : ∀ τ, (simHist A inp bad byz dl d τ).length = τ + 1
  | 0 => rfl
  | τ + 1 => by simp [simHist, simHist_length τ]

/-- Extending the history does not change earlier entries. -/
theorem simHist_getD_succ {τ σ : ℕ} (h : σ ≤ τ) :
    (simHist A inp bad byz dl d (τ + 1)).getD σ [] = (simHist A inp bad byz dl d τ).getD σ [] := by
  simp only [simHist, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [simHist_length]; omega)]

/-- The entry for time `σ` of any longer history is the last entry of `simHist … σ`. -/
theorem simHist_getD_of_le {σ τ : ℕ} (h : σ ≤ τ) :
    (simHist A inp bad byz dl d τ).getD σ [] = (simHist A inp bad byz dl d σ).getD σ [] := by
  induction τ with
  | zero => obtain rfl : σ = 0 := by omega
            rfl
  | succ τ ih =>
    rcases Nat.lt_or_ge σ (τ + 1) with h' | h'
    · rw [simHist_getD_succ _ _ _ _ _ _ (by omega), ih (by omega)]
    · obtain rfl : σ = τ + 1 := by omega
      rfl

/-- The last entry of `simHist … (τ + 1)` is computed by `simNext` from `simHist … τ`. -/
theorem simHist_getD_self_succ (τ : ℕ) :
    (simHist A inp bad byz dl d (τ + 1)).getD (τ + 1) [] =
      simNext A bad byz dl d (simHist A inp bad byz dl d τ) τ := by
  simp only [simHist, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [simHist_length])]
  simp

end simHist

/-- **Memoised simulation.** In a run with faulty set `bad`, the states are given by `simHist`. -/
theorem Run.st_eq_simHist (A : Algorithm (Fin n) M S VI VO) (R : Run (Fin n) M VI)
    {bad : Fin n → Bool} (hbad : ∀ q, bad q = true ↔ q ∈ R.faulty) (d : S) : ∀ τ (p : Fin n),
      R.st A τ p = ((simHist A R.inp bad R.byz R.dl d τ).getD τ []).getD p d := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro p
    rcases τ with _ | τ
    · simp [simHist, List.getD_eq_getElem?_getD]
    · have hs : ∀ σ ≤ τ, ∀ q, R.st A σ q =
          ((simHist A R.inp bad R.byz R.dl d τ).getD σ []).getD q d := fun σ hσ q => by
        rw [ih σ (by omega), simHist_getD_of_le _ _ _ _ _ _ hσ]
      rw [Run.st_succ, simHist_getD_self_succ, simNext, List.getD_ofFn, hs τ le_rfl]
      congr 1
      funext q
      rw [Run.inbox_eq_flatMap]
      refine List.flatMap_congr fun σ hσ => ?_
      simp only [List.mem_range] at hσ
      simp only [Run.dlv]
      split_ifs with h1 h2
      · rw [Run.out_of_faulty _ _ ((hbad q).1 h2)]
      · rw [Run.out_of_correct _ _ (fun h => h2 ((hbad q).2 h)), hs σ (by omega)]
      · rfl

/-! ### Zero delays -/

/-- Memoised computation of the global state at time `τ` of a zero-delay run on `Fin n` (faulty
parties `bad`, Byzantine messages `byz`); `d` is a dummy state for out-of-range indices. -/
def simStates (A : Algorithm (Fin n) M S VI VO) (inp : Fin n → VI) (bad : Fin n → Bool)
    (byz : Fin n → ℕ → Fin n → List M) (d : S) : ℕ → List S
  | 0 => List.ofFn fun p => A.init p (inp p)
  | τ + 1 =>
    let v := simStates A inp bad byz d τ
    List.ofFn fun p => A.step p (v.getD p d) fun q =>
      if bad q then byz q τ p else A.send q (v.getD q d) p

/-- **Memoised simulation of zero-delay runs.** -/
theorem Run.st_eq_simStates (A : Algorithm (Fin n) M S VI VO) {R : Run (Fin n) M VI}
    (hdl : ∀ q τ p, R.dl q τ p = τ) {bad : Fin n → Bool} (hbad : ∀ q, bad q = true ↔ q ∈ R.faulty)
    (d : S) : ∀ τ (p : Fin n), R.st A τ p = (simStates A R.inp bad R.byz d τ).getD p d := by
  intro τ
  induction τ with
  | zero => intro p; simp [simStates]
  | succ τ ih =>
    intro p
    rw [Run.st_succ]
    simp only [simStates, List.getD_ofFn]
    rw [← ih p]
    congr 1
    funext q
    rw [Run.inbox_of_dl_eq _ hdl]
    by_cases hq : q ∈ R.faulty
    · rw [Run.out_of_faulty _ _ hq, ite_eq_left ((hbad q).2 hq)]
    · rw [Run.out_of_correct _ _ hq, ite_eq_right (fun h => hq ((hbad q).1 h)), ih q]

end Cslib.Byzantine.PartialSync
