/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.Action.Defs

/-!
# Being first in a random set under a uniformly random order

Let `π : V ≃ Fin (Fintype.card V)` be a uniformly random order of a finite type `V` (`π v` is the
position of `v`; probabilities are counted over `Finset.univ`). Let `W π` be a random set containing
a fixed element `x` whose value only depends on the relative order of the elements of `W π \ {x}`
and on the relative order of the elements outside `W π` (the position of `x` and the interleaving of
the two groups are arbitrary). Then

  `E[|W| · 1{x is π-first in W} · 1{all of B precede x}] ≤ Pr[all of B precede x]`

(`Cslib.RandomOrder.sum_card_first_le`), and for `B = ∅` even `E[|W| · 1{x is π-first in W}] = 1`
(`Cslib.RandomOrder.sum_card_first_eq`).

The proof groups the orders by the value `P` of `W π` and by the rank of `x` in `P` (the number of
elements of `P` before `x`). Swapping `x` with its `P`-successor is an injection from rank `i` to
rank `i + 1` preserving `W π = P` and the event that `B` precedes `x`; hence rank `0` is the least
likely rank, and it has probability at most `1/|P|` of the event. Swapping with the `P`-predecessor
gives the reverse injection, so for `B = ∅` all ranks are equally likely.
-/

@[expose] public section

open Finset

namespace Cslib.RandomOrder

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of elements of `P` placed by the order `π` strictly before `x`. -/
def rank (π : V ≃ Fin (Fintype.card V)) (x : V) (P : Finset V) : ℕ :=
  #(P.filter fun u => π u < π x)

/-- `π'` is obtained from `π` by swapping the positions of `x` and of its `P`-successor `e`, i.e.
the element of `P` with the smallest position after `x`. -/
def SuccSwap (x : V) (P : Finset V) (π π' : V ≃ Fin (Fintype.card V)) : Prop :=
  ∃ e ∈ P, π x < π e ∧ (∀ u ∈ P, ¬ (π x < π u ∧ π u < π e)) ∧ π' = (Equiv.swap x e).trans π

section Swap

variable (π : V ≃ Fin (Fintype.card V)) (x e : V)

private lemma swap_x : ((Equiv.swap x e).trans π) x = π e := by simp

private lemma swap_e : ((Equiv.swap x e).trans π) e = π x := by simp

private lemma swap_other {u : V} (hu : u ≠ x) (he : u ≠ e) :
    ((Equiv.swap x e).trans π) u = π u := by
  simp [Equiv.swap_apply_of_ne_of_ne hu he]

private lemma swap_swap : (Equiv.swap x e).trans ((Equiv.swap x e).trans π) = π := by
  ext u; simp

end Swap

variable {x : V} {P : Finset V} {π π' : V ≃ Fin (Fintype.card V)}

omit [DecidableEq V] in
private lemma ne_of_pos {π : V ≃ Fin (Fintype.card V)} {u v : V} (h : u ≠ v) : π u ≠ π v :=
  fun h' => h (π.injective h')

/-- Swapping `x` with its `P`-successor preserves the relative order of any two elements other than
`x` that are both in `P` or both outside `P`. -/
private lemma order_swap {e : V} (heP : e ∈ P) (hxe : π x < π e)
    (hbt : ∀ u ∈ P, ¬ (π x < π u ∧ π u < π e)) (u v : V) (hu : u ≠ x) (hv : v ≠ x)
    (huv : u ∈ P ↔ v ∈ P) :
    π u < π v ↔ ((Equiv.swap x e).trans π) u < ((Equiv.swap x e).trans π) v := by
  by_cases hue : u = e <;> by_cases hve : v = e
  · subst hue hve; simp
  · subst hue
    rw [swap_e, swap_other π x _ hv hve]
    have hvP : v ∈ P := huv.mp heP
    have h1 := ne_of_pos (π := π) hv
    have h2 := ne_of_pos (π := π) hve
    have h3 := hbt v hvP
    constructor <;> intro h <;> push Not at h3 <;> omega
  · subst hve
    rw [swap_e, swap_other π x _ hu hue]
    have huP : u ∈ P := huv.mpr heP
    have h1 := ne_of_pos (π := π) hu
    have h2 := ne_of_pos (π := π) hue
    have h3 := hbt u huP
    constructor <;> intro h <;> push Not at h3 <;> omega
  · rw [swap_other π x _ hu hue, swap_other π x _ hv hve]

/-- A value `W π` that only depends on the relative orders inside `W π \ {x}` and outside `W π` is
unchanged by a successor swap. -/
private lemma W_of_succSwap (W : (V ≃ Fin (Fintype.card V)) → Finset V)
    (hW : ∀ π σ : V ≃ Fin (Fintype.card V),
      (∀ u v, u ≠ x → v ≠ x → (u ∈ W π ↔ v ∈ W π) → (π u < π v ↔ σ u < σ v)) → W σ = W π)
    (h : SuccSwap x P π π') (hπ : W π = P) : W π' = P := by
  obtain ⟨e, heP, hxe, hbt, rfl⟩ := h
  rw [hW π _ (fun u v hu hv huv => order_swap heP hxe hbt u v hu hv (hπ ▸ huv)), hπ]

/-- The converse direction of `W_of_succSwap`. -/
private lemma W_of_succSwap' (W : (V ≃ Fin (Fintype.card V)) → Finset V)
    (hW : ∀ π σ : V ≃ Fin (Fintype.card V),
      (∀ u v, u ≠ x → v ≠ x → (u ∈ W π ↔ v ∈ W π) → (π u < π v ↔ σ u < σ v)) → W σ = W π)
    (h : SuccSwap x P π π') (hπ' : W π' = P) : W π = P := by
  obtain ⟨e, heP, hxe, hbt, rfl⟩ := h
  rw [hW _ π (fun u v hu hv huv => (order_swap heP hxe hbt u v hu hv (hπ' ▸ huv)).symm), hπ']

/-- A successor swap keeps every element that precedes `x` before `x`. -/
private lemma prec_of_succSwap {B : Finset V} (h : SuccSwap x P π π')
    (hB : ∀ y ∈ B, π y < π x) : ∀ y ∈ B, π' y < π' x := by
  obtain ⟨e, heP, hxe, hbt, rfl⟩ := h
  intro y hy
  have hyx := hB y hy
  have h1 : y ≠ x := fun h => by rw [h] at hyx; exact lt_irrefl _ hyx
  have h2 : y ≠ e := fun h => by rw [h] at hyx; exact lt_asymm hyx hxe
  rw [swap_x, swap_other π x e h1 h2]
  exact hyx.trans hxe

/-- A successor swap increases the rank of `x` in `P` by one. -/
private lemma rank_of_succSwap (h : SuccSwap x P π π') : rank π' x P = rank π x P + 1 := by
  obtain ⟨e, heP, hxe, hbt, rfl⟩ := h
  have hex : e ≠ x := fun h => by rw [h] at hxe; exact lt_irrefl _ hxe
  have key : P.filter (fun u => ((Equiv.swap x e).trans π) u < ((Equiv.swap x e).trans π) x)
      = insert e (P.filter fun u => π u < π x) := by
    ext u
    simp only [mem_filter, mem_insert, swap_x]
    by_cases hux : u = x
    · rw [hux, swap_x]; simp [hex.symm]
    by_cases hue : u = e
    · rw [hue, swap_e]; simp [heP, hxe]
    rw [swap_other π x e hux hue]
    have h1 := ne_of_pos (π := π) hux
    have h2 := ne_of_pos (π := π) hue
    constructor
    · rintro ⟨huP, hu⟩
      right
      refine ⟨huP, ?_⟩
      have h3 := hbt u huP
      push Not at h3
      omega
    · rintro (h | ⟨huP, hu⟩)
      · exact absurd h hue
      · exact ⟨huP, hu.trans hxe⟩
  unfold rank
  rw [key, card_insert_of_notMem]
  simp [hxe.le]

/-- Every order in which `x` has a `P`-successor admits a successor swap. -/
private lemma exists_succSwap (hxP : x ∈ P) (hr : rank π x P + 1 < #P) :
    ∃ π', SuccSwap x P π π' := by
  have hne : (P.filter fun u => π x < π u).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hemp
    have hsub : P.erase x ⊆ P.filter fun u => π u < π x := by
      intro u hu
      rw [mem_erase] at hu
      rw [mem_filter]
      refine ⟨hu.2, ?_⟩
      have h1 := ne_of_pos (π := π) hu.1
      have h2 : u ∉ P.filter fun u => π x < π u := by rw [hemp]; simp
      rw [mem_filter] at h2
      push Not at h2
      have := h2 hu.2
      omega
    have := card_le_card hsub
    rw [card_erase_of_mem hxP] at this
    unfold rank at hr
    omega
  obtain ⟨e, he, hmin⟩ := exists_min_image _ π hne
  rw [mem_filter] at he
  refine ⟨_, e, he.1, he.2, fun u hu ⟨h1, h2⟩ => ?_, rfl⟩
  exact absurd h2 (not_lt.mpr (hmin u (mem_filter.mpr ⟨hu, h1⟩)))

/-- After a successor swap, the swapped element is the `P`-predecessor of `x`. -/
private lemma pred_of_succSwap (h : SuccSwap x P π π') :
    ∃ e ∈ P, π' e < π' x ∧ (∀ u ∈ P, ¬ (π' e < π' u ∧ π' u < π' x)) ∧
      π = (Equiv.swap x e).trans π' := by
  obtain ⟨e, heP, hxe, hbt, rfl⟩ := h
  refine ⟨e, heP, by rwa [swap_x, swap_e], fun u hu ⟨h1, h2⟩ => ?_, (swap_swap π x e).symm⟩
  rw [swap_e] at h1
  rw [swap_x] at h2
  by_cases hux : u = x
  · rw [hux, swap_x] at h2; exact lt_irrefl _ h2
  by_cases hue : u = e
  · rw [hue, swap_e] at h1; exact lt_irrefl _ h1
  rw [swap_other π x e hux hue] at h1 h2
  exact hbt u hu ⟨h1, h2⟩

/-- A successor swap is injective. -/
private lemma succSwap_inj {π₁ π₂ : V ≃ Fin (Fintype.card V)} (h1 : SuccSwap x P π₁ π')
    (h2 : SuccSwap x P π₂ π') : π₁ = π₂ := by
  obtain ⟨e₁, he₁, hlt₁, hbt₁, rfl⟩ := pred_of_succSwap h1
  obtain ⟨e₂, he₂, hlt₂, hbt₂, rfl⟩ := pred_of_succSwap h2
  have : e₁ = e₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne (ne_of_pos (π := π') hne) with h | h
    · exact hbt₁ e₂ he₂ ⟨h, hlt₂⟩
    · exact hbt₂ e₁ he₁ ⟨h, hlt₁⟩
  rw [this]

/-- The successor swap of an order is unique. -/
private lemma succSwap_unique {π₁ π₂ : V ≃ Fin (Fintype.card V)} (h1 : SuccSwap x P π π₁)
    (h2 : SuccSwap x P π π₂) : π₁ = π₂ := by
  obtain ⟨e₁, he₁, hlt₁, hbt₁, rfl⟩ := h1
  obtain ⟨e₂, he₂, hlt₂, hbt₂, rfl⟩ := h2
  have : e₁ = e₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne (ne_of_pos (π := π) hne) with h | h
    · exact hbt₂ e₁ he₁ ⟨hlt₁, h⟩
    · exact hbt₁ e₂ he₂ ⟨hlt₂, h⟩
  rw [this]

/-- Every order in which `x` has a `P`-predecessor is a successor swap of some order. -/
private lemma exists_succSwap_pred (hr : 0 < rank π' x P) : ∃ π, SuccSwap x P π π' := by
  have hne : (P.filter fun u => π' u < π' x).Nonempty := card_pos.mp hr
  obtain ⟨e, he, hmax⟩ := exists_max_image _ π' hne
  rw [mem_filter] at he
  refine ⟨(Equiv.swap x e).trans π', e, he.1, ?_, fun u hu ⟨h1, h2⟩ => ?_,
    (swap_swap π' x e).symm⟩
  · rw [swap_x, swap_e]; exact he.2
  · rw [swap_x] at h1
    rw [swap_e] at h2
    by_cases hux : u = x
    · rw [hux, swap_x] at h1; exact lt_irrefl _ h1
    by_cases hue : u = e
    · rw [hue, swap_e] at h2; exact lt_irrefl _ h2
    rw [swap_other π' x e hux hue] at h1 h2
    exact absurd h1 (not_lt.mpr (hmax u (mem_filter.mpr ⟨hu, h2⟩)))

omit [DecidableEq V] in
/-- The rank of `x` in a set `P ∋ x` is less than `#P`. -/
private lemma rank_lt (hxP : x ∈ P) : rank π x P < #P := by
  unfold rank
  refine card_lt_card ⟨filter_subset _ _, fun h => ?_⟩
  exact lt_irrefl _ (mem_filter.mp (h hxP)).2

omit [DecidableEq V] in
/-- `x` has rank `0` in `P` iff it precedes every element of `P`. -/
private lemma rank_eq_zero_iff : rank π x P = 0 ↔ ∀ u ∈ P, π x ≤ π u := by
  unfold rank
  rw [card_eq_zero, filter_eq_empty_iff]
  simp only [not_lt]

section Counting

variable (W : (V ≃ Fin (Fintype.card V)) → Finset V)
  (hW : ∀ π σ : V ≃ Fin (Fintype.card V),
    (∀ u v, u ≠ x → v ≠ x → (u ∈ W π ↔ v ∈ W π) → (π u < π v ↔ σ u < σ v)) → W σ = W π)
  {Q : (V ≃ Fin (Fintype.card V)) → Prop} [DecidablePred Q]

include hW in
/-- Among the orders with `W π = P` and `Q π`, rank `i` is at most as likely as rank `i + 1`,
provided `Q` is preserved by successor swaps. -/
private lemma card_rank_le_succ (hQ : ∀ π π', SuccSwap x P π π' → Q π → Q π') (hxP : x ∈ P)
    {i : ℕ} (hi : i + 1 < #P) :
    #(univ.filter fun π => (W π = P ∧ Q π) ∧ rank π x P = i) ≤
      #(univ.filter fun π => (W π = P ∧ Q π) ∧ rank π x P = i + 1) := by
  refine card_le_card_of_forall_subsingleton (SuccSwap x P) (fun π hπ => ?_) (fun π' _ => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hπ
    obtain ⟨π', h⟩ := exists_succSwap hxP (hπ.2 ▸ hi)
    refine ⟨π', ?_, h⟩
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨⟨W_of_succSwap W hW h hπ.1.1, hQ _ _ h hπ.1.2⟩, by rw [rank_of_succSwap h, hπ.2]⟩
  · intro π₁ h₁ π₂ h₂
    exact succSwap_inj h₁.2 h₂.2

include hW in
/-- Among the orders with `W π = P` and `Q π`, rank `i + 1` is at most as likely as rank `i`,
provided `Q` is reflected by successor swaps. -/
private lemma card_rank_succ_le (hQ : ∀ π π', SuccSwap x P π π' → Q π' → Q π) {i : ℕ} :
    #(univ.filter fun π => (W π = P ∧ Q π) ∧ rank π x P = i + 1) ≤
      #(univ.filter fun π => (W π = P ∧ Q π) ∧ rank π x P = i) := by
  refine card_le_card_of_forall_subsingleton (fun π' π => SuccSwap x P π π')
    (fun π' hπ' => ?_) (fun π _ => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hπ'
    obtain ⟨π, h⟩ := exists_succSwap_pred (π' := π') (by rw [hπ'.2]; omega)
    refine ⟨π, ?_, h⟩
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨⟨W_of_succSwap' W hW h hπ'.1.1, hQ _ _ h hπ'.1.2⟩, ?_⟩
    have := rank_of_succSwap h
    omega
  · intro π₁ h₁ π₂ h₂
    exact succSwap_unique h₁.2 h₂.2

/-- Counting the orders with `W π = P` and `Q π` by the rank of `x` in `P`. -/
private lemma card_eq_sum_rank (hxP : x ∈ P) :
    #(univ.filter fun π => W π = P ∧ Q π) =
      ∑ i ∈ range #P, #(univ.filter fun π => (W π = P ∧ Q π) ∧ rank π x P = i) := by
  rw [card_eq_sum_card_fiberwise (f := fun π => rank π x P) (t := range #P)
    (fun π _ => mem_range.mpr (rank_lt hxP))]
  simp only [filter_filter]

include hW in
/-- `#P` times the number of orders with `W π = P`, `Q π` and `x` first in `P` is at most the
number of orders with `W π = P` and `Q π`. -/
private lemma card_mul_le (hQ : ∀ π π', SuccSwap x P π π' → Q π → Q π') (hxP : x ∈ P) :
    #P * #(univ.filter fun π => (W π = P ∧ Q π) ∧ rank π x P = 0) ≤
      #(univ.filter fun π => W π = P ∧ Q π) := by
  have hmono : ∀ i, i < #P → #(univ.filter fun π => (W π = P ∧ Q π) ∧ rank π x P = 0) ≤
      #(univ.filter fun π => (W π = P ∧ Q π) ∧ rank π x P = i) := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih => intro hi; exact (ih (by omega)).trans (card_rank_le_succ W hW hQ hxP hi)
  rw [card_eq_sum_rank W hxP]
  calc #P * #(univ.filter fun π => (W π = P ∧ Q π) ∧ rank π x P = 0)
      = ∑ _i ∈ range #P, #(univ.filter fun π => (W π = P ∧ Q π) ∧ rank π x P = 0) := by simp
    _ ≤ _ := sum_le_sum fun i hi => hmono i (mem_range.mp hi)

include hW in
/-- If `Q` is preserved and reflected by successor swaps, all ranks are equally likely. -/
private lemma card_mul_eq (hQ : ∀ π π', SuccSwap x P π π' → Q π → Q π')
    (hQ' : ∀ π π', SuccSwap x P π π' → Q π' → Q π) (hxP : x ∈ P) :
    #P * #(univ.filter fun π => (W π = P ∧ Q π) ∧ rank π x P = 0) =
      #(univ.filter fun π => W π = P ∧ Q π) := by
  have hconst : ∀ i, i < #P → #(univ.filter fun π => (W π = P ∧ Q π) ∧ rank π x P = i) =
      #(univ.filter fun π => (W π = P ∧ Q π) ∧ rank π x P = 0) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [← ih (by omega)]
      exact le_antisymm (card_rank_succ_le W hW hQ') (card_rank_le_succ W hW hQ hxP hi)
  rw [card_eq_sum_rank W hxP, sum_congr rfl fun i hi => hconst i (mem_range.mp hi)]
  simp

end Counting

/-- Let `W π` be a random set containing `x` whose value does not change when the order `π` is
modified keeping the relative order inside `W π \ {x}` and inside the complement of `W π`. Then
`E[|W| · 1{x is π-first in W} · 1{every element of B precedes x}]`
`≤ Pr[every element of B precedes x]`
for a uniformly random order `π`, stated here after multiplying by `(Fintype.card V)!`. -/
theorem sum_card_first_le (x : V) (B : Finset V)
    (W : (V ≃ Fin (Fintype.card V)) → Finset V)
    (hx : ∀ π, x ∈ W π)
    (hW : ∀ π σ : V ≃ Fin (Fintype.card V),
      (∀ u v, u ≠ x → v ≠ x → (u ∈ W π ↔ v ∈ W π) → (π u < π v ↔ σ u < σ v)) → W σ = W π) :
    ∑ π, (if (∀ y ∈ B, π y < π x) ∧ (∀ u ∈ W π, π x ≤ π u) then (W π).card else 0)
      ≤ (Finset.univ.filter fun π : V ≃ Fin (Fintype.card V) => ∀ y ∈ B, π y < π x).card := by
  rw [← sum_filter, ← sum_fiberwise _ W,
    card_eq_sum_card_fiberwise (f := W) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_le_sum fun P _ => ?_
  rw [sum_congr rfl fun π hπ => by rw [(mem_filter.mp hπ).2], sum_const, smul_eq_mul]
  by_cases hxP : x ∈ P
  · have h := card_mul_le W hW (Q := fun π => ∀ y ∈ B, π y < π x)
      (fun _ _ h hq => prec_of_succSwap h hq) hxP
    rw [mul_comm]
    convert h using 2
    · congr 1
      ext π
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨hq, hf⟩, hw⟩
        exact ⟨⟨hw, hq⟩, rank_eq_zero_iff.mpr (hw ▸ hf)⟩
      · rintro ⟨⟨hw, hq⟩, hr⟩
        exact ⟨⟨hq, by rw [hw]; exact rank_eq_zero_iff.mp hr⟩, hw⟩
    · ext π
      simp only [mem_filter, mem_univ, true_and]
      exact and_comm
  · have : (univ.filter fun π : V ≃ Fin (Fintype.card V) =>
        (∀ y ∈ B, π y < π x) ∧ ∀ u ∈ W π, π x ≤ π u).filter (fun π => W π = P) = ∅ := by
      rw [filter_eq_empty_iff]
      intro π _ hw
      exact hxP (hw ▸ hx π)
    simp [this]

/-- Equality version of `sum_card_first_le` for `B = ∅`: `E[|W| · 1{x is π-first in W}] = 1` for a
uniformly random order `π`, stated here after multiplying by `(Fintype.card V)!`. -/
theorem sum_card_first_eq (x : V)
    (W : (V ≃ Fin (Fintype.card V)) → Finset V)
    (hx : ∀ π, x ∈ W π)
    (hW : ∀ π σ : V ≃ Fin (Fintype.card V),
      (∀ u v, u ≠ x → v ≠ x → (u ∈ W π ↔ v ∈ W π) → (π u < π v ↔ σ u < σ v)) → W σ = W π) :
    ∑ π, (if ∀ u ∈ W π, π x ≤ π u then (W π).card else 0) = (Fintype.card V).factorial := by
  have hfact : (Fintype.card V).factorial = #(univ : Finset (V ≃ Fin (Fintype.card V))) := by
    rw [card_univ, Fintype.card_equiv (Fintype.equivFin V)]
  rw [hfact, ← sum_filter, ← sum_fiberwise _ W,
    card_eq_sum_card_fiberwise (f := W) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun P _ => ?_
  rw [sum_congr rfl fun π hπ => by rw [(mem_filter.mp hπ).2], sum_const, smul_eq_mul]
  by_cases hxP : x ∈ P
  · have h := card_mul_eq W hW (Q := fun _ => True) (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial) hxP
    rw [mul_comm]
    convert h using 2
    · congr 1
      ext π
      simp only [mem_filter, mem_univ, true_and, and_true]
      constructor
      · rintro ⟨hf, hw⟩
        exact ⟨hw, rank_eq_zero_iff.mpr (hw ▸ hf)⟩
      · rintro ⟨hw, hr⟩
        exact ⟨by rw [hw]; exact rank_eq_zero_iff.mp hr, hw⟩
    · ext π
      simp
  · have h1 : (univ.filter fun π : V ≃ Fin (Fintype.card V) =>
        ∀ u ∈ W π, π x ≤ π u).filter (fun π => W π = P) = ∅ := by
      rw [filter_eq_empty_iff]
      intro π _ hw
      exact hxP (hw ▸ hx π)
    have h2 : (univ : Finset (V ≃ Fin (Fintype.card V))).filter (fun π => W π = P) = ∅ := by
      rw [filter_eq_empty_iff]
      intro π _ hw
      exact hxP (hw ▸ hx π)
    simp [h1, h2]

end Cslib.RandomOrder
