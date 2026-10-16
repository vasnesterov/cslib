/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Linarith

/-!
# The isolation lemma

Let `𝓕` be a nonempty family of subsets of a finite ground set `E`. If every element of `E` gets an
integer weight chosen independently and uniformly from a finite set `R`, then the probability that
`𝓕` has more than one minimum-weight member is at most `|⋃𝓕| / |R|`.

We state it in counting form: the number of weight functions `w : E → R` for which the minimum is
not unique, times `|R|`, is at most `|⋃𝓕| * |R| ^ |E|`.

## Main definitions

* `Cslib.Isolation.wt w S`: the weight `∑ e ∈ S, w e` of a set `S`.
* `Cslib.Isolation.UniqueMin 𝓕 w`: `𝓕` has a unique minimum-weight member under `w`.

## Main results

* `Cslib.Isolation.card_not_uniqueMin_le`: the isolation lemma.
* `Cslib.Isolation.card_not_uniqueMin_le_Icc`: the special case `R = [-W, W]`.

## Proof

If the minimum is not unique, some element `e ∈ ⋃𝓕` is *ambiguous*: it lies in one minimizer but
not in another. For fixed `e` and fixed values of `w` off `e`, at most one value of `w e` makes `e`
ambiguous. A union bound over `e` finishes.

## References

* K. Mulmuley, U. V. Vazirani, V. V. Vazirani, *Matching is as easy as matrix inversion*,
  Combinatorica 7 (1987), 105–113.
-/

@[expose] public section

open Finset

namespace Cslib.Isolation

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Weight of a set under integer weights. -/
def wt (w : E → ℤ) (S : Finset E) : ℤ := ∑ e ∈ S, w e

/-- The family `𝓕` has a unique minimum-weight member under `w`. -/
def UniqueMin (𝓕 : Finset (Finset E)) (w : E → ℤ) : Prop :=
  ∃ S ∈ 𝓕, ∀ T ∈ 𝓕, T ≠ S → wt w S < wt w T

instance (𝓕 : Finset (Finset E)) : DecidablePred (UniqueMin 𝓕) := fun w => by
  unfold UniqueMin; infer_instance

/-- `e` is ambiguous for `w`: it belongs to one minimum-weight member of `𝓕` but not to another. -/
def Amb (𝓕 : Finset (Finset E)) (e : E) (w : E → ℤ) : Prop :=
  ∃ S ∈ 𝓕, ∃ T ∈ 𝓕, (∀ U ∈ 𝓕, wt w S ≤ wt w U) ∧ (∀ U ∈ 𝓕, wt w T ≤ wt w U) ∧ e ∈ S ∧ e ∉ T

instance (𝓕 : Finset (Finset E)) (e : E) : DecidablePred (Amb 𝓕 e) := fun w => by
  unfold Amb; infer_instance

omit [Fintype E] in
/-- A non-unique minimum yields an ambiguous element of `⋃𝓕`. -/
lemma exists_amb_of_not_uniqueMin {𝓕 : Finset (Finset E)} (h𝓕 : 𝓕.Nonempty) {w : E → ℤ}
    (h : ¬ UniqueMin 𝓕 w) : ∃ e ∈ 𝓕.biUnion id, Amb 𝓕 e w := by
  obtain ⟨S, hS, hSmin⟩ := 𝓕.exists_min_image (wt w) h𝓕
  simp only [UniqueMin, not_exists, not_and, not_forall, not_lt] at h
  obtain ⟨T, hT, hTS, hle⟩ := h S hS
  have hTmin : ∀ U ∈ 𝓕, wt w T ≤ wt w U := fun U hU => hle.trans (hSmin U hU)
  by_cases hsub : S ⊆ T
  · obtain ⟨e, heT, heS⟩ := not_subset.1 fun h' => hTS (subset_antisymm h' hsub)
    exact ⟨e, mem_biUnion.2 ⟨T, hT, heT⟩, T, hT, S, hS, hTmin, hSmin, heT, heS⟩
  · obtain ⟨e, heS, heT⟩ := not_subset.1 hsub
    exact ⟨e, mem_biUnion.2 ⟨S, hS, heS⟩, S, hS, T, hT, hSmin, hTmin, heS, heT⟩

omit [Fintype E] in
lemma wt_eq_of_eqOn {w w' : E → ℤ} {e : E} (hw : ∀ x, x ≠ e → w x = w' x) (U : Finset E) :
    wt w U = wt w' U + if e ∈ U then w e - w' e else 0 := by
  rw [← sub_eq_iff_eq_add', wt, wt, ← sum_sub_distrib]
  rw [← sum_ite_eq' U e (fun _ => w e - w' e)]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : x = e
  · subst hx; simp
  · simp [hx, hw x hx]

omit [Fintype E] [DecidableEq E] in
/-- Key fact: given the values off `e`, at most one value at `e` makes `e` ambiguous. -/
lemma eq_of_amb {𝓕 : Finset (Finset E)} {e : E} {w w' : E → ℤ} (h : Amb 𝓕 e w)
    (h' : Amb 𝓕 e w') (hw : ∀ x, x ≠ e → w x = w' x) : w e = w' e := by
  classical
  obtain ⟨S₁, hS₁, T₁, hT₁, hS₁m, hT₁m, heS₁, heT₁⟩ := h
  obtain ⟨S₂, hS₂, T₂, hT₂, hS₂m, hT₂m, heS₂, heT₂⟩ := h'
  have eS₁ := wt_eq_of_eqOn hw S₁
  have eT₁ := wt_eq_of_eqOn hw T₁
  have eS₂ := wt_eq_of_eqOn hw S₂
  have eT₂ := wt_eq_of_eqOn hw T₂
  simp only [heS₁, heT₁, heS₂, heT₂, ite_true, ite_false, add_zero] at eS₁ eT₁ eS₂ eT₂
  have h1 := hS₁m T₁ hT₁
  have h2 := hT₁m S₁ hS₁
  have h3 := hS₂m T₂ hT₂
  have h4 := hT₂m S₂ hS₂
  have h5 := hT₁m T₂ hT₂
  have h6 := hT₂m T₁ hT₁
  have h7 := hT₁m S₂ hS₂
  have h8 := hT₂m S₁ hS₁
  linarith

/-- For fixed `e`, at most `|R| ^ (|E| - 1)` weight functions make `e` ambiguous. -/
lemma card_amb_mul_le (𝓕 : Finset (Finset E)) (R : Finset ℤ) (e : E) :
    #((Fintype.piFinset fun _ : E => R).filter (Amb 𝓕 e)) * #R ≤ #R ^ Fintype.card E := by
  set A := (Fintype.piFinset fun _ : E => R).filter (Amb 𝓕 e)
  let f : (E → ℤ) → ({x // x ≠ e} → ℤ) := fun w x => w x
  have hinj : Set.InjOn f A := by
    intro w hw w' hw' hf
    simp only [A, coe_filter, Set.mem_ofPred_eq] at hw hw'
    have hoff : ∀ x, x ≠ e → w x = w' x := fun x hx => congrFun hf ⟨x, hx⟩
    funext x
    by_cases hx : x = e
    · subst hx; exact eq_of_amb hw.2 hw'.2 hoff
    · exact hoff x hx
  have hmaps : Set.MapsTo f A (Fintype.piFinset fun _ : {x // x ≠ e} => R) := by
    intro w hw
    simp only [A, coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset] at hw
    rw [mem_coe, Fintype.mem_piFinset]
    exact fun x => hw.1 x
  have hcard := card_le_card_of_injOn f hmaps hinj
  rw [Fintype.card_piFinset, prod_const, card_univ] at hcard
  have hE : Fintype.card {x // x ≠ e} + 1 = Fintype.card E := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have := Fintype.card_pos_iff.2 ⟨e⟩
    omega
  calc #A * #R ≤ #R ^ Fintype.card {x // x ≠ e} * #R := Nat.mul_le_mul_right _ hcard
    _ = #R ^ Fintype.card E := by rw [← pow_succ, hE]

/-- **Isolation lemma** (Mulmuley–Vazirani–Vazirani), counting form: among weight
functions with values in `R`, at most a `|⋃𝓕| / |R|` fraction fail to isolate a unique
minimum-weight member of `𝓕`. -/
theorem card_not_uniqueMin_le (𝓕 : Finset (Finset E)) (h𝓕 : 𝓕.Nonempty) (R : Finset ℤ) :
    #((Fintype.piFinset fun _ : E => R).filter fun w => ¬ UniqueMin 𝓕 w) * #R ≤
      #(𝓕.biUnion id) * #R ^ Fintype.card E := by
  have hsub : ((Fintype.piFinset fun _ : E => R).filter fun w => ¬ UniqueMin 𝓕 w) ⊆
      (𝓕.biUnion id).biUnion fun e => (Fintype.piFinset fun _ : E => R).filter (Amb 𝓕 e) := by
    intro w hw
    rw [mem_filter] at hw
    obtain ⟨e, he, ha⟩ := exists_amb_of_not_uniqueMin h𝓕 hw.2
    exact mem_biUnion.2 ⟨e, he, mem_filter.2 ⟨hw.1, ha⟩⟩
  calc _ ≤ #((𝓕.biUnion id).biUnion fun e =>
          (Fintype.piFinset fun _ : E => R).filter (Amb 𝓕 e)) * #R :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (∑ e ∈ 𝓕.biUnion id, #((Fintype.piFinset fun _ : E => R).filter (Amb 𝓕 e))) * #R :=
        Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ e ∈ 𝓕.biUnion id, #((Fintype.piFinset fun _ : E => R).filter (Amb 𝓕 e)) * #R :=
        sum_mul _ _ _
    _ ≤ ∑ _e ∈ 𝓕.biUnion id, #R ^ Fintype.card E :=
        sum_le_sum fun e _ => card_amb_mul_le 𝓕 R e
    _ = #(𝓕.biUnion id) * #R ^ Fintype.card E := by rw [sum_const, smul_eq_mul]

/-- The isolation lemma for weights in `[-W, W]` (a set of size `2W + 1`). -/
theorem card_not_uniqueMin_le_Icc (𝓕 : Finset (Finset E)) (h𝓕 : 𝓕.Nonempty) (W : ℕ) :
    #((Fintype.piFinset fun _ : E => Icc (-(W : ℤ)) W).filter fun w => ¬ UniqueMin 𝓕 w) *
        (2 * W + 1) ≤
      #(𝓕.biUnion id) * (2 * W + 1) ^ Fintype.card E := by
  have hR : #(Icc (-(W : ℤ)) W) = 2 * W + 1 := by
    rw [Int.card_Icc]; omega
  simpa [hR] using card_not_uniqueMin_le 𝓕 h𝓕 (Icc (-(W : ℤ)) W)

end Cslib.Isolation
