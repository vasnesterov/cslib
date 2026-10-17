/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.IteratedModel.Basic

/-!
# Concrete iterated models: immediate snapshot, snapshot, and immediate snapshot with boxes

* `iis` — iterated immediate snapshot (one-round views = vertices of the standard chromatic
  subdivision): `i ∈ V_i ⊆ I`, any two participants are comparable (`j ∈ V_i ∨ i ∈ V_j`), and
  `j ∈ V_i → V_j ⊆ V_i`.
* `isnap` — iterated (atomic) snapshot: views form a chain under inclusion.
* `iisTS` — IIS where every round additionally calls a fresh test&set object between write and
  read. The winner is the first caller; since every process calls the object after its write and
  before its read, the winner is seen by every participant (it is in the first concurrency class),
  and conversely every process of the first class can win.
* `iisBC` — IIS augmented with a fresh binary consensus object per round (first proposal wins, so
  the decided value is the input of a process seen by everybody).

All four models are well formed, allow solo executions, have solo-determined boxes, and are
extendable (`Model.WellFormed`, `Model.AllowsSolo`, `Model.SoloDet`, `Model.Extendable`).
Ordered partitions are produced with `rankSees I rk` (process `i` sees the participants of rank
`≤ rk i`).
-/

@[expose] public section

namespace Cslib.Iterated

variable {P : Type}

/-- One-round immediate-snapshot views of the participating set `I`. -/
def IsIS (I : Finset P) (S : P → Finset P) : Prop :=
  (∀ i ∈ I, i ∈ S i ∧ S i ⊆ I) ∧ (∀ i ∈ I, ∀ j ∈ I, j ∈ S i ∨ i ∈ S j) ∧
    (∀ i ∈ I, ∀ j ∈ I, j ∈ S i → S j ⊆ S i)

/-- One-round (atomic) snapshot views of the participating set `I`. -/
def IsSnap (I : Finset P) (S : P → Finset P) : Prop :=
  (∀ i ∈ I, i ∈ S i ∧ S i ⊆ I) ∧ ∀ i ∈ I, ∀ j ∈ I, S i ⊆ S j ∨ S j ⊆ S i

/-- Views of the ordered partition of `I` given by ranks `rk` (smaller rank = earlier). -/
def rankSees (I : Finset P) (rk : P → ℕ) : P → Finset P :=
  fun i => I.filter (fun j => rk j ≤ rk i)

/-- Ranks of a solo run of `i` (then everybody else). -/
def soloRank [DecidableEq P] (i : P) : P → ℕ := fun j => if j = i then 0 else 1

/-- Iterated immediate snapshot. -/
def iis : Model P Unit Unit := ⟨fun I _ => {p | IsIS I p.sees}⟩

/-- Iterated snapshot. -/
def isnap : Model P Unit Unit := ⟨fun I _ => {p | IsSnap I p.sees}⟩

/-- Iterated immediate snapshot augmented with one test&set object per round. -/
def iisTS [DecidableEq P] : Model P Unit Bool :=
  ⟨fun I _ => {p | IsIS I p.sees ∧ ∃ w ∈ I, (∀ i ∈ I, w ∈ p.sees i) ∧
    ∀ i ∈ I, p.out i = decide (i = w)}⟩

/-- Iterated immediate snapshot augmented with one binary consensus object per round. -/
def iisBC : Model P Bool Bool :=
  ⟨fun I a => {p | IsIS I p.sees ∧ ∃ w ∈ I, (∀ i ∈ I, w ∈ p.sees i) ∧ ∀ i ∈ I, p.out i = a w}⟩

section Lemmas

variable {I J : Finset P}

/-- A process sees the participants of rank at most its own. -/
@[simp] lemma mem_rankSees {rk : P → ℕ} {i j : P} : j ∈ rankSees I rk i ↔ j ∈ I ∧ rk j ≤ rk i := by
  simp [rankSees]

/-- The views of an ordered partition are immediate-snapshot views. -/
lemma isIS_rankSees (rk : P → ℕ) : IsIS I (rankSees I rk) := by
  refine ⟨fun i hi => ⟨by simp [hi], fun j => by simp +contextual⟩, fun i hi j hj => ?_,
    fun i _ j _ hji k hk => ?_⟩
  · rcases le_total (rk j) (rk i) with h | h
    · exact Or.inl (by simp [hj, h])
    · exact Or.inr (by simp [hi, h])
  · simp only [mem_rankSees] at *
    exact ⟨hk.1, hk.2.trans hji.2⟩

/-- Immediate-snapshot views are snapshot views. -/
lemma IsIS.isSnap {S : P → Finset P} (h : IsIS I S) : IsSnap I S := by
  refine ⟨h.1, fun i hi j hj => ?_⟩
  rcases h.2.1 i hi j hj with h' | h'
  · exact Or.inr (h.2.2 i hi j hj h')
  · exact Or.inl (h.2.2 j hj i hi h')

/-- In a solo run of `i`, `i` sees only itself. -/
lemma rankSees_solo [DecidableEq P] {i : P} (hi : i ∈ I) : rankSees I (soloRank i) i = {i} := by
  ext j; by_cases hj : j = i <;> simp [soloRank, hj, hi]

/-- In a solo run of `i`, every participant sees `i`. -/
lemma soloRank_self_mem [DecidableEq P] {i : P} (hi : i ∈ I) (k : P) (_hk : k ∈ I) :
    i ∈ rankSees I (soloRank i) k := by
  simp [soloRank, hi]

/-- Extending views of `J` by letting `I \ J` come last (they see everybody). -/
def extendSees [DecidableEq P] (J I : Finset P) (S : P → Finset P) : P → Finset P :=
  fun j => if j ∈ J then S j else I

/-- Extending immediate-snapshot views of `J` by letting `I \ J` come last. -/
lemma IsIS.extend [DecidableEq P] {S : P → Finset P} (h : IsIS J S) (hJI : J ⊆ I) :
    IsIS I (extendSees J I S) := by
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_, fun i hi j hj hji => ?_⟩
  · by_cases hiJ : i ∈ J
    · simp only [extendSees, hiJ, ite_true]
      exact ⟨(h.1 i hiJ).1, (h.1 i hiJ).2.trans hJI⟩
    · simp [extendSees, hiJ, hi]
  · by_cases hiJ : i ∈ J <;> by_cases hjJ : j ∈ J
    · simpa [extendSees, hiJ, hjJ] using h.2.1 i hiJ j hjJ
    · simp [extendSees, hjJ, hi]
    · simp [extendSees, hiJ, hj]
    · simp [extendSees, hiJ, hj]
  · by_cases hiJ : i ∈ J
    · simp only [extendSees, hiJ, ite_true] at hji ⊢
      have hjJ : j ∈ J := (h.1 i hiJ).2 hji
      simpa [extendSees, hjJ] using h.2.2 i hiJ j hjJ hji
    · simp only [extendSees, hiJ, ite_false]
      intro k hk
      by_cases hjJ : j ∈ J
      · simp only [hjJ, ite_true] at hk; exact hJI ((h.1 j hjJ).2 hk)
      · simpa [hjJ] using hk

/-- Extending snapshot views of `J` by letting `I \ J` come last. -/
lemma IsSnap.extend [DecidableEq P] {S : P → Finset P} (h : IsSnap J S) (hJI : J ⊆ I) :
    IsSnap I (extendSees J I S) := by
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · by_cases hiJ : i ∈ J
    · simp only [extendSees, hiJ, ite_true]
      exact ⟨(h.1 i hiJ).1, (h.1 i hiJ).2.trans hJI⟩
    · simp [extendSees, hiJ, hi]
  · by_cases hiJ : i ∈ J <;> by_cases hjJ : j ∈ J
    · simpa [extendSees, hiJ, hjJ] using h.2 i hiJ j hjJ
    · simp only [extendSees, hiJ, hjJ, ite_true, ite_false]
      exact Or.inl ((h.1 i hiJ).2.trans hJI)
    · simp only [extendSees, hiJ, hjJ, ite_true, ite_false]
      exact Or.inr ((h.1 j hjJ).2.trans hJI)
    · simp [extendSees, hiJ, hjJ]

/-- The extended views of the processes of `J` are their original views. -/
lemma extendSees_of_mem [DecidableEq P] {S : P → Finset P} {j : P} (hj : j ∈ J) :
    extendSees J I S j = S j := by
  simp [extendSees, hj]

/-! ### `iis` -/

/-- Iterated immediate snapshot is well formed. -/
lemma iis_wellFormed : (iis : Model P Unit Unit).WellFormed :=
  fun _ _ _ hp i hi => hp.1 i hi

/-- Iterated immediate snapshot allows solo executions. -/
lemma iis_allowsSolo : (iis : Model P Unit Unit).AllowsSolo :=
  fun _ _ i hi => by
    classical
    exact ⟨⟨rankSees _ (soloRank i), fun _ => ()⟩, isIS_rankSees _, rankSees_solo hi⟩

/-- Iterated immediate snapshot has (trivially) solo-determined boxes. -/
lemma iis_soloDet : (iis : Model P Unit Unit).SoloDet (fun _ _ => ()) :=
  fun _ _ _ _ _ _ _ => rfl

/-- Iterated immediate snapshot is extendable. -/
lemma iis_extendable : (iis : Model P Unit Unit).Extendable := by
  classical
  intro J I hJI a p hp
  exact ⟨⟨extendSees J I p.sees, p.out⟩, IsIS.extend hp hJI,
    fun j hj => ⟨extendSees_of_mem hj, rfl⟩⟩

/-! ### `isnap` -/

/-- Iterated snapshot is well formed. -/
lemma isnap_wellFormed : (isnap : Model P Unit Unit).WellFormed :=
  fun _ _ _ hp i hi => hp.1 i hi

/-- Iterated snapshot allows solo executions. -/
lemma isnap_allowsSolo : (isnap : Model P Unit Unit).AllowsSolo :=
  fun _ _ i hi => by
    classical
    exact ⟨⟨rankSees _ (soloRank i), fun _ => ()⟩, (isIS_rankSees _).isSnap, rankSees_solo hi⟩

/-- Iterated snapshot has (trivially) solo-determined boxes. -/
lemma isnap_soloDet : (isnap : Model P Unit Unit).SoloDet (fun _ _ => ()) :=
  fun _ _ _ _ _ _ _ => rfl

/-- Iterated snapshot is extendable. -/
lemma isnap_extendable : (isnap : Model P Unit Unit).Extendable := by
  classical
  intro J I hJI a p hp
  exact ⟨⟨extendSees J I p.sees, p.out⟩, IsSnap.extend hp hJI,
    fun j hj => ⟨extendSees_of_mem hj, rfl⟩⟩

/-! ### `iisTS` -/

/-- Iterated immediate snapshot with test&set is well formed. -/
lemma iisTS_wellFormed [DecidableEq P] : (iisTS : Model P Unit Bool).WellFormed :=
  fun _ _ _ hp i hi => hp.1.1 i hi

/-- Iterated immediate snapshot with test&set allows solo executions. -/
lemma iisTS_allowsSolo [DecidableEq P] : (iisTS : Model P Unit Bool).AllowsSolo := by
  intro I _ i hi
  refine ⟨⟨rankSees I (soloRank i), fun j => decide (j = i)⟩,
    ⟨isIS_rankSees _, i, hi, fun k hk => soloRank_self_mem hi k hk, fun _ _ => rfl⟩,
    rankSees_solo hi⟩

/-- A process running solo wins test&set. -/
lemma iisTS_soloDet [DecidableEq P] : (iisTS : Model P Unit Bool).SoloDet (fun _ _ => true) := by
  rintro I a p ⟨-, w, hw, hwI, hout⟩ i hi hsolo
  have : w = i := by simpa [hsolo] using hwI i hi
  simp [hout i hi, this]

/-- Iterated immediate snapshot with test&set is extendable. -/
lemma iisTS_extendable [DecidableEq P] : (iisTS : Model P Unit Bool).Extendable := by
  rintro J I hJI a p ⟨hIS, w, hw, hwJ, hout⟩
  refine ⟨⟨extendSees J I p.sees, fun j => decide (j = w)⟩,
    ⟨hIS.extend hJI, w, hJI hw, fun i hi => ?_, fun _ _ => rfl⟩,
    fun j hj => ⟨extendSees_of_mem hj, (hout j hj).symm⟩⟩
  by_cases hiJ : i ∈ J
  · change w ∈ extendSees J I p.sees i
    rw [extendSees_of_mem hiJ]; exact hwJ i hiJ
  · simp [extendSees, hiJ, hJI hw]

/-! ### `iisBC` -/

/-- Iterated immediate snapshot with binary consensus is well formed. -/
lemma iisBC_wellFormed : (iisBC : Model P Bool Bool).WellFormed :=
  fun _ _ _ hp i hi => hp.1.1 i hi

/-- Iterated immediate snapshot with binary consensus allows solo executions. -/
lemma iisBC_allowsSolo : (iisBC : Model P Bool Bool).AllowsSolo := by
  classical
  intro I a i hi
  refine ⟨⟨rankSees I (soloRank i), fun _ => a i⟩,
    ⟨isIS_rankSees _, i, hi, fun k hk => soloRank_self_mem hi k hk, fun _ _ => rfl⟩,
    rankSees_solo hi⟩

/-- A process running solo gets its own proposal back from binary consensus. -/
lemma iisBC_soloDet : (iisBC : Model P Bool Bool).SoloDet (fun _ b => b) := by
  rintro I a p ⟨-, w, hw, hwI, hout⟩ i hi hsolo
  have : w = i := by simpa [hsolo] using hwI i hi
  simp [hout i hi, this]

/-- Iterated immediate snapshot with binary consensus is extendable. -/
lemma iisBC_extendable : (iisBC : Model P Bool Bool).Extendable := by
  classical
  rintro J I hJI a p ⟨hIS, w, hw, hwJ, hout⟩
  refine ⟨⟨extendSees J I p.sees, fun _ => a w⟩,
    ⟨hIS.extend hJI, w, hJI hw, fun i hi => ?_, fun _ _ => rfl⟩,
    fun j hj => ⟨extendSees_of_mem hj, (hout j hj).symm⟩⟩
  by_cases hiJ : i ∈ J
  · change w ∈ extendSees J I p.sees i
    rw [extendSees_of_mem hiJ]; exact hwJ i hiJ
  · simp [extendSees, hiJ, hJI hw]

end Lemmas

end Cslib.Iterated
