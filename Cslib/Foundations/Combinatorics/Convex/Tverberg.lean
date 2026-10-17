/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Colorful Carathéodory and Tverberg's theorem

* `exists_colorful_mem_convexHull` — the **colorful Carathéodory theorem** (Bárány 1982): in a
  real vector space of dimension `D`, if each of more than `D` finite sets `C k` contains `p` in its
  convex hull, one can pick one point of every color so that `p` lies in the convex hull of the
  picks;
* `Convex.tverberg_partition` — **Tverberg's theorem** (Tverberg 1966): for `r ≥ 1`, any family
  of more than `(d + 1)(r - 1)` points `y : ι → E` of a `d`-dimensional real vector space
  (repetitions allowed) admits a partition `part : ι → Fin r` into `r` nonempty parts whose convex
  hulls have a common point;
* `exists_weights_of_mem_convexHull_range` — a point of the convex hull of a finite family is a
  convex combination of the whole family.

Mathlib has the case `r = 2` (Radon, `Convex.radon_partition`) and Helly's theorem
(`Convex.helly_theorem`), but neither colorful Carathéodory nor Tverberg.

## Proof route

Sarkaria's proof (Matoušek, *Lectures on Discrete Geometry*, §8.3), with coordinates instead of
tensor products:

1. `exists_colorful_zero_mem_convexHull` — colorful Carathéodory in a finite-dimensional real inner
   product space, by the classical minimal-distance argument: take the point `x` of minimal norm in
   the union of all colorful convex hulls; if `x ≠ 0`, Carathéodory
   (`eq_pos_convex_span_of_mem_convexHull`) writes `x` with linearly independent points on the
   hyperplane `⟪x, ·⟫ = ‖x‖²`, so some color is unused; replacing it by a point of that color with
   `⟪x, a⟫ ≤ 0` contradicts minimality. `exists_colorful_mem_convexHull` transfers it to an
   arbitrary point of an arbitrary finite-dimensional real vector space.
2. `Convex.tverberg_partition_succ` — Sarkaria's lifting: with `w_0, …, w_s ∈ ℝ^s`
   (`Tverberg.sarkariaVec`, `w_j = e_j`, `w_s = -∑ e_j`), the point `y i` gives the color class
   `{(y i, 1) ⊗ w_j | j}` in `ℝ^{(d+1) s}` (`Tverberg.sarkariaTensor`, indexed by
   `Option (Fin d) × Fin s`), whose barycenter is `0`. A colorful choice `j = part i` with `0` in
   its hull gives weights `μ` with `∑ᵢ μᵢ (y i, 1) ⊗ w_{part i} = 0`; the only linear relations
   among the `w_j` are constant, so the sums `∑_{part i = j} μᵢ (y i, 1)` agree for all `j`, which
   yields the Tverberg point.
-/

@[expose] public section

open Finset Module

section Colorful

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open scoped RealInnerProductSpace

/-- A point of minimal norm `x` of a convex set `K` satisfies `‖x‖² ≤ ⟪x, w⟫` for all `w ∈ K`. -/
theorem sq_norm_le_inner_of_forall_norm_le {K : Set V} (hK : Convex ℝ K) {x : V} (hx : x ∈ K)
    (hmin : ∀ w ∈ K, ‖x‖ ≤ ‖w‖) {w : V} (hw : w ∈ K) : ‖x‖ ^ 2 ≤ ⟪x, w⟫ := by
  have : Nonempty K := ⟨⟨x, hx⟩⟩
  have hinf : ‖(0 : V) - x‖ = ⨅ w : K, ‖(0 : V) - w‖ := by
    refine le_antisymm (le_ciInf fun w => by simpa using hmin w w.2) ?_
    exact ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ (⟨x, hx⟩ : K)
  have := (norm_eq_iInf_iff_real_inner_le_zero hK hx).1 hinf w hw
  simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at this
  linarith

/-- **Colorful Carathéodory theorem** (Bárány 1982), version with the origin, in a real inner
product space. If each of more than `dim V` finite sets `C k` contains the origin in its convex
hull, then one can pick one point `c k ∈ C k` of every color so that the origin lies in the convex
hull of the picked points. -/
theorem exists_colorful_zero_mem_convexHull {κ : Type*} [Fintype κ] [FiniteDimensional ℝ V]
    (C : κ → Finset V) (hC : ∀ k, (0 : V) ∈ convexHull ℝ (C k : Set V))
    (hκ : finrank ℝ V < Fintype.card κ) :
    ∃ c : κ → V, (∀ k, c k ∈ C k) ∧ (0 : V) ∈ convexHull ℝ (Set.range c) := by
  classical
  -- the finite set of colorful choices and the union of their convex hulls
  set S : Set (κ → V) := Set.univ.pi fun k => (C k : Set V) with hS
  have hSfin : S.Finite := Set.Finite.pi fun k => (C k).finite_toSet
  set K := ⋃ c ∈ S, convexHull ℝ (Set.range c) with hK
  have hKc : IsCompact K :=
    hSfin.isCompact_biUnion fun c _ => (Set.finite_range c).isCompact_convexHull (𝕜 := ℝ)
  have hne : ∀ k, (C k).Nonempty := fun k => by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := hC k
    simp [h] at this
  have : Nonempty κ := Fintype.card_pos_iff.1 (by omega)
  let c₀ : κ → V := fun k => (hne k).choose
  have hc₀ : c₀ ∈ S := fun k _ => (hne k).choose_spec
  have hKne : K.Nonempty :=
    ⟨c₀ (Classical.arbitrary κ), Set.mem_iUnion₂.2
      ⟨c₀, hc₀, subset_convexHull ℝ _ (Set.mem_range_self _)⟩⟩
  -- a point of `K` of minimal norm
  obtain ⟨x, hxK, hxmin⟩ := hKc.exists_isMinOn hKne continuous_norm.continuousOn
  obtain ⟨c, hcS, hxc⟩ := Set.mem_iUnion₂.1 hxK
  refine ⟨c, fun k => hcS k (Set.mem_univ _), ?_⟩
  suffices x = 0 by rwa [← this]
  by_contra hx0
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  have hmin : ∀ c' ∈ S, ∀ w ∈ convexHull ℝ (Set.range c'), ‖x‖ ≤ ‖w‖ :=
    fun c' hc' w hw => hxmin (Set.mem_iUnion₂.2 ⟨c', hc', hw⟩)
  have hacute : ∀ w ∈ convexHull ℝ (Set.range c), ‖x‖ ^ 2 ≤ ⟪x, w⟫ := fun w hw =>
    sq_norm_le_inner_of_forall_norm_le (convex_convexHull ℝ _) hxc (hmin c hcS) hw
  -- Carathéodory: `x` is a positive combination of affinely independent points of `range c`
  obtain ⟨ι', _, p, μ, hpc, hpind, hμpos, hμsum, hμx⟩ := eq_pos_convex_span_of_mem_convexHull hxc
  -- all these points lie on the hyperplane `⟪x, ·⟫ = ‖x‖²`
  have hpH : ∀ i, ⟪x, p i⟫ = ‖x‖ ^ 2 := by
    have hge : ∀ i, ‖x‖ ^ 2 ≤ ⟪x, p i⟫ := fun i =>
      hacute _ (subset_convexHull ℝ _ (hpc (Set.mem_range_self i)))
    have hsum : ∑ i, μ i * (⟪x, p i⟫ - ‖x‖ ^ 2) = 0 := by
      have h1 : ∑ i, μ i * ⟪x, p i⟫ = ‖x‖ ^ 2 := by
        calc ∑ i, μ i * ⟪x, p i⟫ = ⟪x, ∑ i, μ i • p i⟫ := by simp [inner_sum, inner_smul_right]
          _ = ‖x‖ ^ 2 := by rw [hμx, real_inner_self_eq_norm_sq]
      simp only [mul_sub, Finset.sum_sub_distrib, h1, ← Finset.sum_mul, hμsum, one_mul, sub_self]
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (hμpos j).le (sub_nonneg.2 (hge j)))).1 hsum i (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hμpos i).ne'
    · linarith
  -- hence they are linearly independent, so there are at most `dim V` of them
  have hplin : LinearIndependent ℝ p := by
    rw [linearIndependent_iff']
    intro s g hg
    refine affineIndependent_iff.1 hpind s g ?_ hg
    have : ⟪x, ∑ i ∈ s, g i • p i⟫ = (∑ i ∈ s, g i) * ‖x‖ ^ 2 := by
      rw [inner_sum, Finset.sum_mul]
      simp [inner_smul_right, hpH]
    rw [hg, inner_zero_right] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact h
    · exact absurd h hx2.ne'
  have hcard : Fintype.card ι' < Fintype.card κ := hplin.fintype_card_le_finrank.trans_lt hκ
  -- some color `k` is not needed to express `x`
  have : ∀ i, ∃ k, c k = p i := fun i => hpc (Set.mem_range_self i)
  choose σ hσ using this
  obtain ⟨k, hk⟩ : ∃ k, ∀ i, σ i ≠ k := by
    by_contra h
    push Not at h
    exact absurd (Fintype.card_le_of_surjective σ fun k => (h k)) (by omega)
  -- a point of color `k` on the other side of the hyperplane through the origin
  obtain ⟨a, haC, ha⟩ : ∃ a ∈ C k, ⟪x, a⟫ ≤ 0 := by
    by_contra h
    push Not at h
    have hsub : (C k : Set V) ⊆ {w | 0 < ⟪x, w⟫} := fun w hw => h w hw
    have hconv : Convex ℝ {w : V | 0 < ⟪x, w⟫} :=
      convex_halfSpace_gt (f := fun w => ⟪x, w⟫) ⟨fun _ _ => inner_add_right _ _ _,
        fun _ _ => inner_smul_right _ _ _⟩ 0
    have := convexHull_min hsub hconv (hC k)
    simp at this
  -- swapping in `a` contradicts the minimality of `x`
  set c' := Function.update c k a
  have hc'S : c' ∈ S := by
    intro j _
    by_cases hj : j = k
    · subst hj; simpa [c'] using haC
    · simpa [c', hj] using hcS j (Set.mem_univ _)
  have hxc' : x ∈ convexHull ℝ (Set.range c') := by
    refine mem_convexHull_of_exists_fintype μ p (fun i => (hμpos i).le) hμsum (fun i => ?_) hμx
    exact ⟨σ i, by simp [c', hk i, hσ i]⟩
  have hac' : a ∈ convexHull ℝ (Set.range c') :=
    subset_convexHull ℝ _ ⟨k, by simp [c']⟩
  have := sq_norm_le_inner_of_forall_norm_le (convex_convexHull ℝ _) hxc' (hmin c' hc'S) hac'
  linarith

end Colorful

section General

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A point of the convex hull of a finite family is a convex combination of the whole family. -/
theorem exists_weights_of_mem_convexHull_range {ι : Type*} [Fintype ι] {v : ι → E} {x : E}
    (hx : x ∈ convexHull ℝ (Set.range v)) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • v i = x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, hw₀, hw₁, rfl⟩ := hx
  have hw₁' : ∑ i, (s : Set ι).indicator w i = 1 := by
    rw [← hw₁, Finset.sum_indicator_subset _ (Finset.subset_univ s)]
  refine ⟨(s : Set ι).indicator w, fun i => ?_, hw₁', ?_⟩
  · by_cases hi : i ∈ s
    · simp [hi, hw₀ i hi]
    · simp [hi]
  · rw [Finset.affineCombination_indicator_subset _ _ (Finset.subset_univ s),
      Finset.affineCombination_eq_linear_combination _ _ _ hw₁']

/-- **Colorful Carathéodory theorem** (Bárány 1982). In a real vector space of dimension `D`, if
each of `D + 1` (or more) finite sets `C k` contains the point `p` in its convex hull, then one
can pick one point `c k ∈ C k` of every color so that `p` lies in the convex hull of the picked
points. -/
theorem exists_colorful_mem_convexHull [FiniteDimensional ℝ E] {κ : Type*} [Fintype κ]
    (C : κ → Finset E) (p : E) (hC : ∀ k, p ∈ convexHull ℝ (C k : Set E))
    (hκ : finrank ℝ E < Fintype.card κ) :
    ∃ c : κ → E, (∀ k, c k ∈ C k) ∧ p ∈ convexHull ℝ (Set.range c) := by
  classical
  set W := EuclideanSpace ℝ (Fin (finrank ℝ E))
  let e : E ≃ₗ[ℝ] W := LinearEquiv.ofFinrankEq E W (by simp [W])
  let g : E →ᵃ[ℝ] W := e.toLinearMap.toAffineMap - AffineMap.const ℝ E (e p)
  have hg : ∀ v, g v = e v - e p := fun v => rfl
  have hgi : ∀ v, g v = 0 ↔ v = p := fun v => by simp [hg, sub_eq_zero]
  obtain ⟨c', hc'C, hc'⟩ := exists_colorful_zero_mem_convexHull (V := W)
    (fun k => (C k).image g) (fun k => by
      rw [Finset.coe_image, ← AffineMap.image_convexHull]
      exact ⟨p, hC k, (hgi p).2 rfl⟩) (by simpa [W] using hκ)
  have : ∀ k, ∃ v ∈ C k, g v = c' k := fun k => Finset.mem_image.1 (hc'C k)
  choose c hcC hc using this
  refine ⟨c, hcC, ?_⟩
  have hrange : Set.range c' = g '' Set.range c := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun k => (hc k).symm)
  rw [hrange, ← AffineMap.image_convexHull] at hc'
  obtain ⟨z, hz, hz0⟩ := hc'
  rwa [(hgi z).1 hz0] at hz

end General

namespace Tverberg

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Sarkaria's vectors `w_0, …, w_s ∈ ℝ^s`: `w_j = e_j` for `j < s` and
`w_s = -(e_0 + ⋯ + e_{s-1})`.
They sum to zero and every `s` of them are linearly independent. -/
def sarkariaVec {s : ℕ} (j : Fin (s + 1)) (l : Fin s) : ℝ :=
  (if j = l.castSucc then 1 else 0) - (if j = Fin.last s then 1 else 0)

/-- Sarkaria's vectors sum to zero. -/
theorem sum_sarkariaVec {s : ℕ} (l : Fin s) : ∑ j, sarkariaVec j l = 0 := by
  simp [sarkariaVec, Finset.sum_sub_distrib]

/-- The point `y` lifted to `ℝ^{d+1}` (coordinates in the basis `finBasis`, plus a constant `1`
in coordinate `none`). -/
noncomputable def liftPt (x : E) : Option (Fin (finrank ℝ E)) → ℝ :=
  fun o => o.elim 1 fun k => (Module.finBasis ℝ E).repr x k

/-- Sarkaria's tensor `liftPt y ⊗ w_j ∈ ℝ^{(d+1) s}`. -/
noncomputable def sarkariaTensor {s : ℕ} (x : E) (j : Fin (s + 1)) :
    Option (Fin (finrank ℝ E)) × Fin s → ℝ :=
  fun q => liftPt x q.1 * sarkariaVec j q.2


end Tverberg

namespace Convex

open Tverberg

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Tverberg's theorem with `s + 1` parts, proved via Sarkaria's lifting and the colorful
Carathéodory theorem. -/
theorem tverberg_partition_succ (s : ℕ) (y : ι → E)
    (hcard : (finrank ℝ E + 1) * s < Fintype.card ι) :
    ∃ part : ι → Fin (s + 1), ∃ z : E, ∀ j, z ∈ convexHull ℝ (y '' {i | part i = j}) := by
  classical
  set d := finrank ℝ E
  -- the color classes `C i = {liftPt (y i) ⊗ w_j | j}`
  let C : ι → Finset (Option (Fin d) × Fin s → ℝ) := fun i =>
    Finset.univ.image (sarkariaTensor (y i))
  have hC : ∀ i, (0 : Option (Fin d) × Fin s → ℝ) ∈ convexHull ℝ (C i : Set _) := by
    intro i
    refine mem_convexHull_of_exists_fintype (fun _ : Fin (s + 1) => (1 / (s + 1 : ℝ)))
      (sarkariaTensor (y i)) (fun _ => by positivity) ?_ (fun j => by simp [C]) ?_
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
    · funext q
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sarkariaTensor, Pi.zero_apply]
      rw [← Finset.mul_sum, ← Finset.mul_sum, sum_sarkariaVec, mul_zero, mul_zero]
  have hdim : finrank ℝ (Option (Fin d) × Fin s → ℝ) < Fintype.card ι := by
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_option] using hcard
  obtain ⟨c, hcC, hc0⟩ := exists_colorful_mem_convexHull C 0 hC hdim
  have : ∀ i, ∃ j, sarkariaTensor (y i) j = c i := fun i => by
    simpa [C] using hcC i
  choose part hpart using this
  have hrange : Set.range c = Set.range fun i => sarkariaTensor (y i) (part i) := by
    simp [hpart]
  rw [hrange] at hc0
  obtain ⟨μ, hμ0, hμ1, hμ⟩ := exists_weights_of_mem_convexHull_range hc0
  -- the weighted lifted sums over each part
  set U : Fin (s + 1) → Option (Fin d) → ℝ :=
    fun j o => ∑ i ∈ Finset.univ.filter (fun i => part i = j), μ i * liftPt (y i) o with hU
  have hUcoord : ∀ o (l : Fin s), U l.castSucc o - U (Fin.last s) o = 0 := by
    intro o l
    have := congrFun hμ (o, l)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sarkariaTensor, Pi.zero_apply,
      sarkariaVec] at this
    rw [← this]
    simp only [hU, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  have hUeq : ∀ j o, U j o = U (Fin.last s) o := by
    intro j o
    induction j using Fin.lastCases with
    | last => rfl
    | cast l => linarith [hUcoord o l]
  have hUsum : ∑ j, U j none = 1 := by
    simp only [hU, liftPt, Option.elim_none, mul_one]
    rw [Finset.sum_fiberwise]
    exact hμ1
  have hUlast : U (Fin.last s) none = 1 / (s + 1 : ℝ) := by
    simp only [hUeq _ none, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hUsum
    push_cast at hUsum
    field_simp
    linarith
  -- the Tverberg point
  set b := Module.finBasis ℝ E
  have hrepr : ∀ j k, b.repr (∑ i ∈ Finset.univ.filter (fun i => part i = j), μ i • y i) k =
      U j (some k) := by
    intro j k
    simp [hU, liftPt, map_sum, Finset.sum_apply, b]
  have hsumeq : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => part i = j), μ i • y i =
      ∑ i ∈ Finset.univ.filter (fun i => part i = Fin.last s), μ i • y i := by
    intro j
    refine b.ext_elem fun k => ?_
    rw [hrepr, hrepr, hUeq]
  refine ⟨part, (s + 1 : ℝ) • ∑ i ∈ Finset.univ.filter (fun i => part i = Fin.last s),
    μ i • y i, fun j => ?_⟩
  rw [← hsumeq j, Finset.smul_sum]
  simp_rw [smul_smul]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => by have := hμ0 i; positivity) ?_
    (fun i hi => subset_convexHull ℝ _ ⟨i, by simpa using hi, rfl⟩)
  rw [← Finset.mul_sum]
  have : ∑ i ∈ Finset.univ.filter (fun i => part i = j), μ i = U j none := by
    simp [hU, liftPt]
  rw [this, hUeq, hUlast]
  field_simp

/-- **Tverberg's theorem** (Tverberg 1966). Any `(d + 1)(r - 1) + 1`
(or more) points `y i` of a `d`-dimensional real vector space, `r ≥ 1`, can be partitioned into
`r` nonempty parts whose convex hulls have a common point. Points may repeat (multiset version). -/
theorem tverberg_partition {r : ℕ} (hr : 0 < r) (y : ι → E)
    (hcard : (finrank ℝ E + 1) * (r - 1) < Fintype.card ι) :
    ∃ part : ι → Fin r, (∀ j, ∃ i, part i = j) ∧
      (⋂ j, convexHull ℝ (y '' {i | part i = j})).Nonempty := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  obtain ⟨part, z, hz⟩ := tverberg_partition_succ s y (by simpa using hcard)
  refine ⟨part, fun j => ?_, z, Set.mem_iInter.2 hz⟩
  by_contra h
  push Not at h
  have hj := hz j
  have hempty : {i | part i = j} = ∅ := Set.eq_empty_of_forall_notMem fun i hi => h i hi
  rw [hempty, Set.image_empty, convexHull_empty] at hj
  exact hj


end Convex
