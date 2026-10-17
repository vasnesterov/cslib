/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Probability.UniformOn
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Uniform probability on a finite type, by counting

Many probabilistic arguments in distributed computing draw finitely many independent uniform
choices (labels, radii, samples), so the sample space is a finite type `Ω` (typically a product
`∀ i, α i`) with the uniform distribution. Probabilities are then ratios of cardinalities, and no
measure theory is needed. This file collects the facts that such arguments use again and again.

## Main definitions

* `Cslib.Probability.uprob E`: the probability `#{ω | E ω} / |Ω|` of an event `E : Ω → Prop`
  (`uprob_eq_dens`: it is Mathlib's `Finset.dens` of the event; `uprob_eq_uniformOn`: it is the
  measure-theoretic `ProbabilityTheory.uniformOn Set.univ`).

## Main statements

* basic laws: `uprob_mono`, `uprob_le_one`, `uprob_not` (complement), `uprob_exists_le` (union
  bound; counting form `card_filter_exists_le`), `uprob_or_le`, `one_sub_sub_le_uprob_and`,
  `uprob_le_iff` (cross-multiplied form);
* probabilistic method: `exists_of_uprob_pos`, `exists_not_of_uprob_lt_one` (for weighted
  averages see `Cslib.Probability.exists_le_of_sum_mul_le` in `Product.lean`);
* independence on product spaces: `uprob_pi`;
* fibres (one coordinate at a time): `card_mul_card_filter_and` (exact fibre decomposition),
  `card_filter_and_le_fiber`, `uprob_and_le_fiber`;
* adaptive sequential choices: `uprob_forall_le_pow` and its counting form
  `pow_mul_card_filter_forall_le` — if each bad event depends only on the choices made so far and
  the last choice makes it happen with probability `≤ q` whatever the past, then all of `S`
  happen with probability `≤ q ^ |S|`;
* many independent rare events: `card_many_le` — at least `t` of `n` independent
  events of probability `≤ a` happen with probability `≤ 2^n a^t`; Chernoff bound by counting
  `uprob_lt_card_filter_mem_le` — more than `c` of the uniform coordinates fall into `B` with
  probability `≤ (1 + |B|/|X|)^n / 2^c`;
* sampling with replacement (Chebyshev by counting): `card_freq_dev_ge_le` — the empirical
  frequency of `P` in `k` uniform samples is `δ`-far from its true frequency for at most a
  `1 / (k δ²)` fraction of the samples.

The counting forms (`card_*`) are stated in `ℕ` or in an arbitrary linearly ordered field, so they
can be used in `ℚ` as well as in `ℝ`; the `uprob_*` forms are in `ℝ`.
-/

@[expose] public section

open Finset

namespace Cslib.Probability

/-! ### Uniform probability of an event -/

section uprob

variable {Ω : Type*} [Fintype Ω]

/-- Probability of an event under the uniform distribution on a finite type:
`#{ω | E ω} / |Ω|` (and `0` if `Ω` is empty). -/
noncomputable def uprob (E : Ω → Prop) : ℝ := (Nat.card {ω // E ω} : ℝ) / Fintype.card Ω

/-- `uprob E = #{ω | E ω} / |Ω|`, with a `Finset` filter. -/
theorem uprob_eq_card_filter (E : Ω → Prop) [DecidablePred E] :
    uprob E = (#(univ.filter E) : ℝ) / Fintype.card Ω := by
  rw [uprob, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- `uprob` is the density (`Finset.dens`) of the event. -/
theorem uprob_eq_dens (E : Ω → Prop) [DecidablePred E] :
    uprob E = ((univ.filter E).dens : ℝ) := by
  rw [uprob_eq_card_filter, dens]; push_cast; rfl

/-- Probabilities are nonnegative. -/
theorem uprob_nonneg (E : Ω → Prop) : 0 ≤ uprob E := by unfold uprob; positivity

/-- Monotonicity: a smaller event has smaller probability. -/
theorem uprob_mono {E E' : Ω → Prop} (h : ∀ ω, E ω → E' ω) : uprob E ≤ uprob E' := by
  classical
  rw [uprob_eq_card_filter, uprob_eq_card_filter]
  gcongr
  exact h _

/-- Probabilities are at most `1`. -/
theorem uprob_le_one (E : Ω → Prop) : uprob E ≤ 1 := by
  classical
  rw [uprob_eq_card_filter]
  rcases (Fintype.card Ω).eq_zero_or_pos with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast (card_filter_le _ _).trans (by simp)

/-- The impossible event has probability `0`. -/
@[simp]
theorem uprob_false : uprob (fun _ : Ω => False) = 0 := by
  classical
  simp [uprob_eq_card_filter]

/-- The sure event has probability `1` (unless the sample space is empty). -/
theorem uprob_true : uprob (fun _ : Ω => True) = if Fintype.card Ω = 0 then 0 else 1 := by
  classical
  rw [uprob_eq_card_filter]
  split_ifs with h
  · simp [h]
  · simp [filter_true_of_mem, div_self (by exact_mod_cast h : (Fintype.card Ω : ℝ) ≠ 0)]

/-- Complement rule. -/
theorem uprob_not [Nonempty Ω] (E : Ω → Prop) : uprob (fun ω => ¬ E ω) = 1 - uprob E := by
  classical
  rw [uprob_eq_card_filter, uprob_eq_card_filter]
  have hpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset Ω)) E
  rw [card_univ] at this
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos.ne']
  exact_mod_cast (add_comm _ _).trans this

/-- `uprob E ≤ ε` is the cross-multiplied counting statement `#{ω | E ω} ≤ ε |Ω|`. -/
theorem uprob_le_iff [Nonempty Ω] (E : Ω → Prop) [DecidablePred E] {ε : ℝ} :
    uprob E ≤ ε ↔ (#(univ.filter E) : ℝ) ≤ ε * Fintype.card Ω := by
  rw [uprob_eq_card_filter, div_le_iff₀ (by exact_mod_cast Fintype.card_pos)]

/-- **Union bound (counting form).** -/
theorem card_filter_exists_le {ι : Type*} (s : Finset ι) (E : ι → Ω → Prop)
    [∀ i, DecidablePred (E i)] [DecidablePred fun ω => ∃ i ∈ s, E i ω] :
    #(univ.filter fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, #(univ.filter (E i)) := by
  classical
  have : univ.filter (fun ω => ∃ i ∈ s, E i ω) = s.biUnion fun i => univ.filter (E i) := by
    ext ω; simp
  rw [this]
  exact card_biUnion_le

/-- **Union bound.** -/
theorem uprob_exists_le {ι : Type*} (s : Finset ι) (E : ι → Ω → Prop) :
    uprob (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, uprob (E i) := by
  classical
  simp only [uprob_eq_card_filter, ← Finset.sum_div]
  gcongr
  exact_mod_cast card_filter_exists_le s E

/-- Union bound for two events. -/
theorem uprob_or_le (E E' : Ω → Prop) : uprob (fun ω => E ω ∨ E' ω) ≤ uprob E + uprob E' := by
  classical
  have h := uprob_exists_le (Ω := Ω) (univ : Finset Bool) (fun b ω => if b then E ω else E' ω)
  simp only [mem_univ, true_and, Fintype.sum_bool, ite_true] at h
  refine le_trans (uprob_mono fun ω hω => ?_) h
  rcases hω with h1 | h1
  · exact ⟨true, by simpa using h1⟩
  · exact ⟨false, by simpa using h1⟩

/-- `Pr[A ∧ B] ≥ 1 - Pr[¬A] - Pr[¬B]`. -/
theorem one_sub_sub_le_uprob_and [Nonempty Ω] (A B : Ω → Prop) :
    1 - uprob (fun ω => ¬ A ω) - uprob (fun ω => ¬ B ω) ≤ uprob (fun ω => A ω ∧ B ω) := by
  have h1 := uprob_or_le (fun ω => ¬ A ω) (fun ω => ¬ B ω)
  have h2 : uprob (fun ω => A ω ∧ B ω) = 1 - uprob (fun ω => ¬ A ω ∨ ¬ B ω) := by
    rw [← uprob_not]; congr 1; ext ω; tauto
  linarith

/-- **Probabilistic method.** An event of positive probability happens for some outcome. -/
theorem exists_of_uprob_pos {E : Ω → Prop} (h : 0 < uprob E) : ∃ ω, E ω := by
  by_contra hc
  push Not at hc
  have : uprob E = 0 := by
    rw [show E = fun _ => False from funext fun ω => propext ⟨hc ω, False.elim⟩, uprob_false]
  linarith

/-- **Probabilistic method.** If an event has probability `< 1`, it fails for some outcome. -/
theorem exists_not_of_uprob_lt_one [Nonempty Ω] {E : Ω → Prop} (h : uprob E < 1) :
    ∃ ω, ¬ E ω :=
  exists_of_uprob_pos (by rw [uprob_not]; linarith)

/-- Bridge to measure theory: `uprob` is the uniform probability measure
`ProbabilityTheory.uniformOn Set.univ` (for any measurable space with measurable singletons). -/
theorem uprob_eq_uniformOn [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (E : Ω → Prop) :
    uprob E = (ProbabilityTheory.uniformOn (Set.univ : Set Ω) {ω | E ω}).toReal := by
  classical
  rw [ProbabilityTheory.uniformOn_univ, MeasureTheory.Measure.count_apply_finite _ (Set.toFinite _),
    ENNReal.toReal_div, uprob_eq_card_filter]
  simp only [ENNReal.toReal_natCast]
  congr 3
  ext ω; simp

end uprob

/-! ### Product spaces: independence and fibres -/

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]

/-- **Independence on product spaces.** Under the uniform distribution on `∀ i, α i`, the
coordinates are independent: `Pr[∀ i, P i (x i)] = ∏ i, Pr[P i]`. -/
theorem uprob_pi (P : ∀ i, α i → Prop) :
    uprob (fun x : ∀ i, α i => ∀ i, P i (x i)) = ∏ i, uprob (P i) := by
  classical
  unfold uprob
  rw [Finset.prod_div_distrib]
  have e : {x : ∀ i, α i // ∀ i, P i (x i)} ≃ ∀ i, {a // P i a} := Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_pi, Fintype.card_pi]
  push_cast
  rfl

/-- The involution `(x, a) ↦ (update x w a, x w)` of `(∀ i, α i) × α w`. -/
private def updateSwap (w : ι) : (∀ i, α i) × α w ≃ (∀ i, α i) × α w where
  toFun p := (Function.update p.1 w p.2, p.1 w)
  invFun p := (Function.update p.1 w p.2, p.1 w)
  left_inv p := by simp
  right_inv p := by simp

/-- **Fibre decomposition.** If `A` ignores coordinate `w`, then
`|α w| · #{A ∧ B} = ∑_{x ∈ A} #{a | B (update x w a)}`: resampling coordinate `w` of a point of
`A` is uniform. -/
theorem card_mul_card_filter_and (w : ι) {A B : (∀ i, α i) → Prop} [DecidablePred A]
    [DecidablePred B] (hA : ∀ x a, A (Function.update x w a) ↔ A x) :
    Fintype.card (α w) * #(univ.filter fun x => A x ∧ B x) =
      ∑ x ∈ univ.filter A, #(univ.filter fun a => B (Function.update x w a)) := by
  let f : (∀ i, α i) → ℕ := fun x => if A x ∧ B x then 1 else 0
  have h1 : ∑ p : (∀ i, α i) × α w, f (Function.update p.1 w p.2) =
      Fintype.card (α w) * #(univ.filter fun x => A x ∧ B x) := by
    rw [show ∑ p : (∀ i, α i) × α w, f (Function.update p.1 w p.2) =
        ∑ p, f ((updateSwap w) p).1 from rfl, Equiv.sum_comp (updateSwap w) (fun p => f p.1),
      Fintype.sum_prod_type]
    simp only [sum_const, card_univ, smul_eq_mul]
    rw [← Finset.mul_sum, Finset.card_filter]
  rw [← h1, Fintype.sum_prod_type, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : A x
  · simp only [f, hA, hx, true_and, ite_true]
    rw [Finset.card_filter]
  · simp [f, hA, hx]

/-- **Fibre bound (counting form).** If `A` ignores coordinate `w` and, whatever the other
coordinates, at most `c` values of coordinate `w` satisfy `B`, then
`|α w| · #{A ∧ B} ≤ c · #{A}`. -/
theorem card_filter_and_le_fiber (w : ι) {A B : (∀ i, α i) → Prop} [DecidablePred A]
    [DecidablePred B] (hA : ∀ x a, A (Function.update x w a) ↔ A x) (c : ℕ)
    (hB : ∀ x, #(univ.filter fun a => B (Function.update x w a)) ≤ c) :
    Fintype.card (α w) * #(univ.filter fun x => A x ∧ B x) ≤ c * #(univ.filter A) := by
  calc Fintype.card (α w) * #(univ.filter fun x => A x ∧ B x)
      = ∑ x ∈ univ.filter A, #(univ.filter fun a => B (Function.update x w a)) :=
        card_mul_card_filter_and w hA
    _ ≤ ∑ _x ∈ univ.filter A, c := sum_le_sum fun x _ => hB x
    _ = c * #(univ.filter A) := by rw [sum_const, smul_eq_mul, mul_comm]

/-- **Fibre bound.** If `A` ignores coordinate `w` and, whatever the other coordinates, a uniform
value of coordinate `w` satisfies `B` with probability at most `q`, then
`Pr[A ∧ B] ≤ q · Pr[A]`. -/
theorem uprob_and_le_fiber (w : ι) {A B : (∀ i, α i) → Prop}
    (hA : ∀ x a, A (Function.update x w a) ↔ A x) {q : ℝ}
    (hB : ∀ x, uprob (fun a => B (Function.update x w a)) ≤ q) :
    uprob (fun x => A x ∧ B x) ≤ q * uprob A := by
  classical
  rcases (Fintype.card (α w)).eq_zero_or_pos with h0 | hpos
  · -- `α w` is empty, hence so is the sample space
    have : IsEmpty (∀ i, α i) := by
      have := Fintype.card_eq_zero_iff.1 h0
      exact ⟨fun x => isEmptyElim (x w)⟩
    simp [uprob, Fintype.card_eq_zero]
  have hB' : ∀ x, (#(univ.filter fun a => B (Function.update x w a)) : ℝ) ≤
      q * Fintype.card (α w) := fun x => by
    have := hB x
    rwa [uprob_eq_card_filter, div_le_iff₀ (by exact_mod_cast hpos)] at this
  have key : (Fintype.card (α w) : ℝ) * #(univ.filter fun x => A x ∧ B x) ≤
      q * Fintype.card (α w) * #(univ.filter A) := by
    have := card_mul_card_filter_and w (B := B) hA
    calc (Fintype.card (α w) : ℝ) * #(univ.filter fun x => A x ∧ B x)
        = ∑ x ∈ univ.filter A, (#(univ.filter fun a => B (Function.update x w a)) : ℝ) := by
          exact_mod_cast this
      _ ≤ ∑ _x ∈ univ.filter A, q * Fintype.card (α w) := sum_le_sum fun x _ => hB' x
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  rw [uprob_eq_card_filter, uprob_eq_card_filter, mul_div_assoc']
  gcongr
  have hc : (0 : ℝ) < Fintype.card (α w) := by exact_mod_cast hpos
  nlinarith

/-- **Adaptive sequential choices.** Let the coordinates be chosen one after the other along a
linear order, and let `bad w` depend only on the coordinates `≤ w`. If, whatever the earlier
choices, the choice of coordinate `w` makes `bad w` happen with probability at most `q`, then all
`bad w`, `w ∈ S`, happen together with probability at most `q ^ |S|`. -/
theorem uprob_forall_le_pow [LinearOrder ι] {bad : ι → (∀ i, α i) → Prop}
    (hdep : ∀ w x y, (∀ z ≤ w, x z = y z) → (bad w x ↔ bad w y)) {q : ℝ} (hq : 0 ≤ q)
    (hfib : ∀ w x, uprob (fun a => bad w (Function.update x w a)) ≤ q) (S : Finset ι) :
    uprob (fun x => ∀ w ∈ S, bad w x) ≤ q ^ #S := by
  induction S using Finset.induction_on_max with
  | empty => simpa using uprob_le_one _
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem has, pow_succ']
    have hA : ∀ x b, (∀ w ∈ s, bad w (Function.update x a b)) ↔ (∀ w ∈ s, bad w x) := by
      intro x b
      refine forall₂_congr fun w hw => hdep w _ _ (fun z hz => ?_)
      rw [Function.update_of_ne (ne_of_lt (hz.trans_lt (hlt w hw)))]
    have h := uprob_and_le_fiber a (A := fun x => ∀ w ∈ s, bad w x) (B := bad a) hA (hfib a)
    calc uprob (fun x => ∀ w ∈ insert a s, bad w x)
        = uprob (fun x => (∀ w ∈ s, bad w x) ∧ bad a x) := by
          congr 1; ext x; simp [and_comm]
      _ ≤ q * uprob (fun x => ∀ w ∈ s, bad w x) := h
      _ ≤ q * q ^ #s := by gcongr

/-- **Adaptive sequential choices (counting form).** As `uprob_forall_le_pow` with
`q = 1 / r`: if at most a `1 / r` fraction of the values of coordinate `w` make `bad w` happen,
whatever the earlier coordinates, then `r ^ |S| · #{x | ∀ w ∈ S, bad w x} ≤ |∀ i, α i|`. -/
theorem pow_mul_card_filter_forall_le [LinearOrder ι] {bad : ι → (∀ i, α i) → Prop}
    [∀ w, DecidablePred (bad w)]
    (hdep : ∀ w x y, (∀ z ≤ w, x z = y z) → (bad w x ↔ bad w y)) (r : ℕ)
    (hfib : ∀ w x, r * #(univ.filter fun a => bad w (Function.update x w a)) ≤
      Fintype.card (α w)) (S : Finset ι) :
    r ^ #S * #(univ.filter fun x : ∀ i, α i => ∀ w ∈ S, bad w x) ≤
      Fintype.card (∀ i, α i) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rcases S.eq_empty_or_nonempty with rfl | hS
    · simp
    · simp [zero_pow (card_ne_zero.2 hS)]
  rcases isEmpty_or_nonempty (∀ i, α i) with hΩ | hΩ
  · simp
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h := uprob_forall_le_pow hdep (q := 1 / r) (by positivity) (fun w x => by
    have hw : Nonempty (α w) := ⟨hΩ.some w⟩
    rw [uprob_eq_card_filter, div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos) hr',
      one_mul, mul_comm]
    exact_mod_cast hfib w x) S
  rw [uprob_eq_card_filter, div_le_iff₀ (by exact_mod_cast Fintype.card_pos), one_div_pow,
    div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h
  rw [mul_comm]
  exact_mod_cast h

end Pi

/-! ### Many independent rare events -/

section Many

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]

/-- **Many independent rare events (counting form).** If each coordinate `i` satisfies `P i`
for at most an `a ≤ 1` fraction of its values, then at most `2^|ι| a^t |∀ i, β i|` points have at
least `t` coordinates satisfying `P`. (Union over the sets `T` of `≥ t` bad coordinates, product
structure.) -/
theorem card_many_le (P : ∀ i, β i → Prop) [∀ i, DecidablePred (P i)] {a : K} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hP : ∀ i, (#(univ.filter (P i)) : K) ≤ a * Fintype.card (β i)) (t : ℕ) :
    (#(univ.filter fun x : ∀ i, β i => t ≤ #(univ.filter fun i => P i (x i))) : K) ≤
      2 ^ Fintype.card ι * a ^ t * Fintype.card (∀ i, β i) := by
  classical
  set N : K := (Fintype.card (∀ i, β i) : K)
  let box : Finset ι → Finset (∀ i, β i) := fun T =>
    Fintype.piFinset fun i => if i ∈ T then univ.filter (P i) else univ
  have hsub : (univ.filter fun x : ∀ i, β i => t ≤ #(univ.filter fun i => P i (x i))) ⊆
      (univ.filter fun T : Finset ι => t ≤ #T).biUnion box := by
    intro x hx
    rw [mem_filter] at hx
    rw [mem_biUnion]
    refine ⟨univ.filter fun i => P i (x i), by simpa using hx.2, ?_⟩
    rw [Fintype.mem_piFinset]
    intro i
    split_ifs with hi
    · simpa using hi
    · exact mem_univ _
  have hT : ∀ T : Finset ι, t ≤ #T → (#(box T) : K) ≤ a ^ t * N := by
    intro T hT
    simp only [box, Fintype.card_piFinset, N, Fintype.card_pi]
    push_cast
    calc ∏ i, ((#(if i ∈ T then univ.filter (P i) else univ) : ℕ) : K)
        ≤ ∏ i, ((if i ∈ T then a else 1) * Fintype.card (β i)) := by
          refine prod_le_prod₀ (fun _ _ => by positivity) fun i _ => ?_
          split_ifs
          · exact hP i
          · simp
      _ = a ^ #T * ∏ i, (Fintype.card (β i) : K) := by
          rw [prod_mul_distrib, prod_ite_mem, univ_inter, prod_const]
      _ ≤ a ^ t * ∏ i, (Fintype.card (β i) : K) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ha0 ha1 hT) (by positivity)
  calc (#(univ.filter fun x : ∀ i, β i => t ≤ #(univ.filter fun i => P i (x i))) : K)
      ≤ (#((univ.filter fun T : Finset ι => t ≤ #T).biUnion box) : K) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ T ∈ univ.filter fun T : Finset ι => t ≤ #T, (#(box T) : K) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _T ∈ univ.filter fun T : Finset ι => t ≤ #T, a ^ t * N :=
        sum_le_sum fun T hTm => hT T (mem_filter.1 hTm).2
    _ ≤ ∑ _T : Finset ι, a ^ t * N :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
    _ = 2 ^ Fintype.card ι * a ^ t * N := by
        simp [Fintype.card_finset, mul_assoc]

/-- The moment generating function at `log 2` of the number of coordinates in `B`:
`∑_x 2^{#{i | x i ∈ B}} = (|X| + |B|)^|ι|`. -/
theorem sum_two_pow_card_filter_mem {X : Type*} [Fintype X] [DecidableEq X] (B : Finset X) :
    ∑ x : ι → X, (2 : ℝ) ^ #(univ.filter fun i => x i ∈ B) =
      ((Fintype.card X : ℝ) + #B) ^ Fintype.card ι := by
  have h1 : ∀ x : ι → X, (2 : ℝ) ^ #(univ.filter fun i => x i ∈ B) =
      ∏ i, (if x i ∈ B then (2 : ℝ) else 1) := by
    intro x
    rw [Finset.prod_ite, prod_const, prod_const_one, mul_one]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (_ : ι) (a : X) => if a ∈ B then (2 : ℝ) else 1), prod_const,
    card_univ]
  congr 1
  rw [Finset.sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, filter_mem_eq_inter,
    univ_inter]
  have := card_filter_add_card_filter_not (s := (univ : Finset X)) (· ∈ B)
  rw [filter_mem_eq_inter, univ_inter, card_univ] at this
  have h : ((#(univ.filter fun a => a ∉ B) : ℕ) : ℝ) = Fintype.card X - #B := by
    rw [eq_sub_iff_add_eq]; exact_mod_cast by omega
  rw [h]; ring

/-- **Chernoff bound (counting form).** For a uniform `x : ι → X` and any real `c`, the number
of coordinates falling into `B` exceeds `c` with probability at most
`(1 + |B| / |X|)^|ι| / 2^c` (Markov's inequality for `2^{#{i | x i ∈ B}}`). -/
theorem uprob_lt_card_filter_mem_le {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (B : Finset X) (c : ℝ) :
    uprob (fun x : ι → X => c < #(univ.filter fun i => x i ∈ B)) ≤
      (1 + #B / (Fintype.card X : ℝ)) ^ Fintype.card ι / (2 : ℝ) ^ c := by
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [uprob_eq_card_filter, Fintype.card_fun]
  have h2c : (0 : ℝ) < (2 : ℝ) ^ c := by positivity
  set A := univ.filter fun x : ι → X => c < #(univ.filter fun i => x i ∈ B)
  -- Markov: `#A · 2^c ≤ ∑ 2^X`
  have hmarkov : (#A : ℝ) * (2 : ℝ) ^ c ≤ ((Fintype.card X : ℝ) + #B) ^ Fintype.card ι := by
    rw [← sum_two_pow_card_filter_mem B]
    calc (#A : ℝ) * (2 : ℝ) ^ c = ∑ x ∈ A, (2 : ℝ) ^ c := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ A, (2 : ℝ) ^ #(univ.filter fun i => x i ∈ B) := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (mem_filter.mp hx).2.le
      _ ≤ ∑ x : ι → X, (2 : ℝ) ^ #(univ.filter fun i => x i ∈ B) :=
          Finset.sum_le_sum_of_subset_of_nonneg (subset_univ A) (fun _ _ _ => by positivity)
  rw [div_le_div_iff₀ (by positivity) h2c]
  calc (#A : ℝ) * (2 : ℝ) ^ c ≤ ((Fintype.card X : ℝ) + #B) ^ Fintype.card ι := hmarkov
    _ = (1 + #B / (Fintype.card X : ℝ)) ^ Fintype.card ι *
          ((Fintype.card X ^ Fintype.card ι : ℕ) : ℝ) := by
        push_cast
        rw [← mul_pow]; congr 1; field_simp

end Many

/-! ### Sampling with replacement: Chebyshev by counting -/

section Sampling

variable {K : Type*} {Y : Type*} [Fintype Y]

/-- Splitting a sum over `(k+1)`-tuples into the first entry and the rest. -/
private lemma sum_fun_succ {M : Type*} [AddCommMonoid M] {k : ℕ} (F : (Fin (k + 1) → Y) → M) :
    ∑ g, F g = ∑ y, ∑ g : Fin k → Y, F (Fin.cons y g) := by
  rw [← (Fin.consEquiv fun _ => Y).sum_comp, Fintype.sum_prod_type]
  rfl

/-- First moment: a centred function summed along a uniform `k`-tuple has mean zero. -/
theorem sum_sum_comp_eq_zero [CommRing K] (h : Y → K) (h0 : ∑ y, h y = 0) (k : ℕ) :
    ∑ g : Fin k → Y, ∑ j, h (g j) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_fun_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sum_add_distrib, ih, sum_const,
      card_univ, nsmul_eq_mul, add_zero]
    simp [h0, ← mul_sum]

/-- Second moment: for a centred `h`, `|Y| · ∑_g (∑_j h (g j))² = k |Y|^k ∑_y h y²` (the cross
terms vanish by independence). -/
theorem card_mul_sum_sq_sum_comp [CommRing K] (h : Y → K) (h0 : ∑ y, h y = 0) (k : ℕ) :
    (Fintype.card Y : K) * ∑ g : Fin k → Y, (∑ j, h (g j)) ^ 2 =
      k * (Fintype.card Y : K) ^ k * ∑ y, h y ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_fun_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hy : ∀ y, ∑ g : Fin k → Y, (h y + ∑ j, h (g j)) ^ 2 =
        (Fintype.card Y : K) ^ k * h y ^ 2 + 2 * h y * ∑ g : Fin k → Y, ∑ j, h (g j) +
          ∑ g : Fin k → Y, (∑ j, h (g j)) ^ 2 := by
      intro y
      simp only [add_sq, sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    simp only [hy, sum_sum_comp_eq_zero h h0, mul_zero, add_zero, sum_add_distrib, sum_const,
      card_univ, nsmul_eq_mul, mul_add, ih, ← mul_sum]
    push_cast
    ring

/-- **Chebyshev's inequality for sampling with replacement (counting form).** Among all
`g : Fin k → Y`, at most `|Y|^k / (k δ²)` have an empirical frequency of `P` that deviates by at
least `δ` from the true frequency of `P` in `Y`. -/
theorem card_freq_dev_ge_le [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Nonempty Y]
    (P : Y → Prop) [DecidablePred P] {k : ℕ} (hk : 0 < k)
    {δ : K} (hδ : 0 < δ) :
    ((#(univ.filter fun g : Fin k → Y => δ ≤
        |(#(univ.filter fun j => P (g j)) : K) / k -
          (#(univ.filter P) : K) / Fintype.card Y|) : ℕ) : K) ≤
      (Fintype.card Y : K) ^ k / (k * δ ^ 2) := by
  set N : K := (Fintype.card Y : K) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast Fintype.card_pos
  set q : K := (#(univ.filter P) : K) / N with hq
  set h : Y → K := fun y => (if P y then 1 else 0) - q with hh
  have h0 : ∑ y, h y = 0 := by
    simp only [hh, sum_sub_distrib, sum_boole, sum_const, card_univ, nsmul_eq_mul]
    rw [hq, ← hNdef]
    field_simp
    ring
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one hN, hNdef]
    exact_mod_cast card_le_univ _
  have hsq : ∑ y, h y ^ 2 ≤ N := by
    calc ∑ y, h y ^ 2 ≤ ∑ _y : Y, (1 : K) := by
          refine sum_le_sum fun y _ => ?_
          simp only [hh]
          split_ifs
          · nlinarith
          · nlinarith
      _ = N := by simp [hNdef]
  have hs : ∀ g : Fin k → Y, ∑ j, h (g j) = (#(univ.filter fun j => P (g j)) : K) - k * q := by
    intro g
    simp [hh, sum_sub_distrib, sum_boole]
  have hk' : (0 : K) < k := by exact_mod_cast hk
  have hmom : ∑ g : Fin k → Y, (∑ j, h (g j)) ^ 2 ≤ k * N ^ k := by
    have := card_mul_sum_sq_sum_comp h h0 k
    rw [← hNdef] at this
    have h2 : N * ∑ g : Fin k → Y, (∑ j, h (g j)) ^ 2 ≤ N * (k * N ^ k) := by
      rw [this]
      calc (k : K) * N ^ k * ∑ y, h y ^ 2 ≤ k * N ^ k * N := by gcongr
        _ = N * (k * N ^ k) := by ring
    exact le_of_mul_le_mul_left h2 hN
  set A := univ.filter fun g : Fin k → Y => δ ≤
        |(#(univ.filter fun j => P (g j)) : K) / k - q| with hA
  have hcard : (#A : K) * (k * δ) ^ 2 ≤ k * N ^ k := by
    calc (#A : K) * (k * δ) ^ 2 = ∑ _g ∈ A, (k * δ) ^ 2 := by simp
      _ ≤ ∑ g ∈ A, (∑ j, h (g j)) ^ 2 := by
          refine sum_le_sum fun g hg => ?_
          rw [hA, mem_filter] at hg
          have e : ∑ j, h (g j) = k * ((#(univ.filter fun j => P (g j)) : K) / k - q) := by
            rw [hs]; field_simp
          have hle : (k : K) * δ ≤ |(k : K) * ((#(univ.filter fun j => P (g j)) : K) / k - q)| := by
            rw [abs_mul, abs_of_pos hk']
            exact mul_le_mul_of_nonneg_left hg.2 hk'.le
          rw [e]
          exact (pow_le_pow_left₀ (by positivity) hle 2).trans (sq_abs _).le
      _ ≤ ∑ g : Fin k → Y, (∑ j, h (g j)) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
      _ ≤ k * N ^ k := hmom
  rw [le_div_iff₀ (by positivity)]
  calc (#A : K) * (k * δ ^ 2) = (#A * (k * δ) ^ 2) / k := by field_simp
    _ ≤ (k * N ^ k) / k := by gcongr
    _ = N ^ k := by field_simp

end Sampling

end Cslib.Probability
