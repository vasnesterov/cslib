/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi

/-!
# i.i.d. coin fields

Infinitely many i.i.d. `Bernoulli(p)` coins indexed by a type `ι` (`true` with probability `p`), as
the infinite product measure `coinMeasure p := Measure.infinitePi (fun _ => Ber(true, false, p))` on
`ι → Bool`. This is the measure-theoretic counterpart of the finite `Cslib.Probability.coinProb`
(`Cslib/Probability/Finite/Bernoulli.lean`); Mathlib's `ProbabilityTheory.setBernoulli` is the same
product viewed as a random set.

* `Determined S J` — the event `S` depends only on the coins indexed by the finite set `J`
  (`determined_iff_dependsOn`: Mathlib's `DependsOn` for the predicate `· ∈ S`); such events are
  measurable (`Determined.measurableSet`), and events determined by disjoint index sets are
  independent (`coinMeasure_inter`).
* `coinMeasure_forall_eq_false` — `P(all coins in J are false) = (1 - p)^{|J|}`;
  `coinMeasure_real_coord` — `P(ω i = b) = p` or `1 - p`;
  `coinMeasure_real_partition` — splitting an event along a finitely determined function.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace Cslib.Probability

variable {ι : Type*}

/-- i.i.d. `Bernoulli(p)` coins indexed by `ι` (`true` with probability `p`). -/
noncomputable def coinMeasure (p : I) : Measure (ι → Bool) :=
  Measure.infinitePi (fun _ : ι => Ber(true, false, p))

instance (p : I) : IsProbabilityMeasure (coinMeasure (ι := ι) p) := by
  unfold coinMeasure; infer_instance

/-- The event `S` depends only on the coordinates in `J`. -/
def Determined (S : Set (ι → Bool)) (J : Finset ι) : Prop :=
  ∀ ω ω' : ι → Bool, (∀ i ∈ J, ω i = ω' i) → (ω ∈ S ↔ ω' ∈ S)

/-- `Determined` is Mathlib's `DependsOn` for the indicator predicate of `S`. -/
theorem determined_iff_dependsOn {S : Set (ι → Bool)} {J : Finset ι} :
    Determined S J ↔ DependsOn (· ∈ S) (J : Set ι) :=
  ⟨fun h _ _ hxy => propext (h _ _ hxy), fun h _ _ hω => (h hω).to_iff⟩

namespace Determined

variable {S T : Set (ι → Bool)} {J K : Finset ι}

/-- The complement of an event determined by `J` is determined by `J`. -/
theorem compl (h : Determined S J) : Determined Sᶜ J :=
  fun ω ω' hω => not_congr (h ω ω' hω)

/-- An event determined by `J` is determined by every superset of `J`. -/
theorem mono (h : Determined S J) (hJK : J ⊆ K) : Determined S K :=
  fun ω ω' hω => h ω ω' fun i hi => hω i (hJK hi)

/-- The intersection of events determined by `J` and `K` is determined by `J ∪ K`. -/
theorem inter [DecidableEq ι] (hS : Determined S J) (hT : Determined T K) :
    Determined (S ∩ T) (J ∪ K) := fun ω ω' hω =>
  and_congr (hS.mono Finset.subset_union_left ω ω' hω) (hT.mono Finset.subset_union_right ω ω' hω)

/-- An event determined by `J` is the preimage of its restriction to the coordinates `J`. -/
theorem preimage_eq (h : Determined S J) :
    S = (fun ω (i : J) => ω i) ⁻¹' ((fun ω (i : J) => ω i) '' S) := by
  ext ω
  constructor
  · intro hω; exact ⟨ω, hω, rfl⟩
  · rintro ⟨ω', hω', heq⟩
    exact (h ω' ω fun i hi => congrFun heq ⟨i, hi⟩).1 hω'

/-- An event determined by finitely many coins is measurable. -/
theorem measurableSet (h : Determined S J) : MeasurableSet S := by
  rw [h.preimage_eq]
  have hm : Measurable (fun (ω : ι → Bool) (i : J) => ω i) := by fun_prop
  exact hm (Set.toFinite _).measurableSet

end Determined

/-- Events determined by disjoint sets of coins are independent. -/
theorem coinMeasure_inter (p : I) {S T : Set (ι → Bool)} {J K : Finset ι} (hS : Determined S J)
    (hT : Determined T K) (hJK : Disjoint J K) :
    coinMeasure p (S ∩ T) = coinMeasure p S * coinMeasure p T := by
  classical
  have hi : iIndepFun (fun i (ω : ι → Bool) => ω i) (coinMeasure (ι := ι) p) :=
    iIndepFun_infinitePi (X := fun _ (b : Bool) => b) fun _ => measurable_id
  have hind := hi.indepFun_finset J K hJK fun i => measurable_pi_apply i
  rw [hS.preimage_eq, hT.preimage_eq]
  exact hind.measure_inter_preimage_eq_mul _ _ (Set.toFinite _).measurableSet
    (Set.toFinite _).measurableSet

/-- `P(all coins in J are false) = (1-p)^{|J|}`. -/
theorem coinMeasure_forall_eq_false (p : I) (J : Finset ι) :
    coinMeasure p {ω : ι → Bool | ∀ i ∈ J, ω i = false} = ((toNNReal (σ p) : ℝ≥0∞)) ^ J.card := by
  have : {ω : ι → Bool | ∀ i ∈ J, ω i = false} = Set.pi (↑J) (fun _ => {false}) := by
    ext ω; simp [Set.mem_pi]
  rw [this, coinMeasure, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp

/-- "All coins in `J` are `false`" is determined by `J`. -/
theorem determined_forall_eq_false (J : Finset ι) :
    Determined {ω : ι → Bool | ∀ i ∈ J, ω i = false} J := fun ω ω' h => by
  simp only [Set.mem_ofPred_eq]
  exact forall₂_congr fun i hi => by rw [h i hi]

/-- `P(ω i = b) = p` or `1 - p`. -/
theorem coinMeasure_real_coord (p : I) (i : ι) (b : Bool) :
    (coinMeasure p).real {ω : ι → Bool | ω i = b} = if b then (p : ℝ) else 1 - p := by
  classical
  have : {ω : ι → Bool | ω i = b} = Set.pi (↑({i} : Finset ι)) (fun _ => {b}) := by
    ext ω; simp
  rw [measureReal_def, this, coinMeasure,
    Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  cases b <;> simp [coe_symm_eq]

/-- "Coin `i` is `b`" is determined by `{i}`. -/
theorem determined_coord (i : ι) (b : Bool) : Determined {ω : ι → Bool | ω i = b} {i} :=
  fun ω ω' h => by simp only [Set.mem_ofPred_eq, h i (Finset.mem_singleton_self i)]

/-- `coinMeasure_inter` for `Measure.real`. -/
theorem coinMeasure_real_inter (p : I) {S T : Set (ι → Bool)} {J K : Finset ι} (hS : Determined S J)
    (hT : Determined T K) (hJK : Disjoint J K) :
    (coinMeasure p).real (S ∩ T) = (coinMeasure p).real S * (coinMeasure p).real T := by
  simp only [measureReal_def, coinMeasure_inter p hS hT hJK, ENNReal.toReal_mul]

/-- Splitting an event along the fibres of a finitely determined function. -/
theorem coinMeasure_real_partition {β : Type*} (p : I) {A : Set (ι → Bool)}
    {J : Finset ι} (hA : Determined A J) (F : (ι → Bool) → β)
    (hF : ∀ y, Determined {ω | F ω = y} J) (s : Finset β) (hs : ∀ ω ∈ A, F ω ∈ s) :
    (coinMeasure p).real A = ∑ y ∈ s, (coinMeasure p).real (A ∩ {ω | F ω = y}) := by
  classical
  have hU : A = ⋃ y ∈ s, (A ∩ {ω | F ω = y}) := by
    ext ω; simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, exists_prop]
    exact ⟨fun h => ⟨_, hs ω h, h, rfl⟩, fun ⟨_, _, h, _⟩ => h⟩
  conv_lhs => rw [hU]
  refine measureReal_biUnion_finset ?_ fun y _ => (hA.inter (hF y)).measurableSet
  intro y _ y' _ hyy'
  refine Set.disjoint_left.2 fun ω h1 h2 => hyy' ?_
  exact h1.2.symm.trans h2.2

end Cslib.Probability
