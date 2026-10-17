/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sums over a finite type after changing one value

Potential-function arguments sum a quantity over all processes and change it at one process per
step. This file provides the corresponding facts about `∑ x, f x` when `f` is changed at a single
point:

* `Finset.sum_update_add`, `Fintype.sum_update_add` — `∑ x, update f a b x + f a = ∑ x, f x + b`
  (over a finset containing `a`, resp. over a finite type), and `Fintype.sum_comp_update_add` for
  `g ∘ update f a b`;
* `Fintype.sum_le_sum_of_eq_off`, `Fintype.sum_lt_sum_of_eq_off` — if `g` agrees with `f` outside
  `a`, then the sums compare as `g a` and `f a`;
* `Fintype.sum_lt_sum_of_update` — decreasing one value decreases the sum;
* `Fintype.sum_lt_sum_of_le_add` — a large drop at one point outweighs bounded increases elsewhere.
-/

@[expose] public section

open Finset

namespace Finset

variable {α M : Type*} [AddCommMonoid M] [DecidableEq α]

/-- Changing `f` at `a ∈ s` to `b` changes the sum over `s` by replacing `f a` with `b`. -/
theorem sum_update_add {s : Finset α} {a : α} (h : a ∈ s) (f : α → M) (b : M) :
    ∑ x ∈ s, Function.update f a b x + f a = ∑ x ∈ s, f x + b := by
  rw [Finset.sum_update_of_mem h, Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase _ _ h]
  ac_rfl

end Finset

namespace Fintype

variable {α M : Type*} [Fintype α]

section AddCommMonoid

variable [AddCommMonoid M] [DecidableEq α]

/-- Changing `f` at `a` to `b` changes the sum by replacing `f a` with `b`. -/
theorem sum_update_add (f : α → M) (a : α) (b : M) :
    ∑ x, Function.update f a b x + f a = ∑ x, f x + b :=
  Finset.sum_update_add (Finset.mem_univ a) f b

/-- Changing `f` at `a` to `b` changes `∑ x, g (f x)` by replacing `g (f a)` with `g b`. -/
theorem sum_comp_update_add {β : Type*} (g : β → M) (f : α → β) (a : α) (b : β) :
    ∑ x, g (Function.update f a b x) + g (f a) = ∑ x, g (f x) + g b := by
  have := sum_update_add (g ∘ f) a (g b)
  rwa [← Function.comp_update] at this

end AddCommMonoid

section Ordered

variable [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]

/-- If `g` agrees with `f` outside `a` and `g a ≤ f a`, then `∑ g ≤ ∑ f`. -/
theorem sum_le_sum_of_eq_off {f g : α → M} (a : α) (h : ∀ x, x ≠ a → g x = f x)
    (ha : g a ≤ f a) : ∑ x, g x ≤ ∑ x, f x :=
  Finset.sum_le_sum fun x _ => by
    by_cases hx : x = a
    · exact hx ▸ ha
    · exact (h x hx).le

/-- If `g` agrees with `f` outside `a` and `g a < f a`, then `∑ g < ∑ f`. -/
theorem sum_lt_sum_of_eq_off {f g : α → M} (a : α) (h : ∀ x, x ≠ a → g x = f x)
    (ha : g a < f a) : ∑ x, g x < ∑ x, f x :=
  Finset.sum_lt_sum (fun x _ => by
    by_cases hx : x = a
    · exact hx ▸ ha.le
    · exact (h x hx).le) ⟨a, Finset.mem_univ _, ha⟩

/-- Decreasing the value at one point decreases the sum. -/
theorem sum_lt_sum_of_update [DecidableEq α] {f : α → M} {a : α} {b : M} (h : b < f a) :
    ∑ x, Function.update f a b x < ∑ x, f x :=
  sum_lt_sum_of_eq_off a (fun _ hx => Function.update_of_ne hx _ _) (by simpa using h)

/-- If `g` exceeds `f` by at most `c` outside `a`, and at `a` drops by more than the total possible
increase `(card α - 1) • c` elsewhere, then `∑ g < ∑ f`. -/
theorem sum_lt_sum_of_le_add {f g : α → M} {c : M} (a : α) (h : ∀ x, x ≠ a → g x ≤ f x + c)
    (ha : g a + (Fintype.card α - 1) • c < f a) : ∑ x, g x < ∑ x, f x := by
  classical
  rw [← Finset.add_sum_erase _ g (Finset.mem_univ a),
    ← Finset.add_sum_erase _ f (Finset.mem_univ a)]
  have h₁ : ∑ x ∈ univ.erase a, g x ≤ ∑ x ∈ univ.erase a, f x + (Fintype.card α - 1) • c := by
    rw [← Finset.card_univ, ← Finset.card_erase_of_mem (Finset.mem_univ a), ← Finset.sum_const,
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x hx => h x (Finset.ne_of_mem_erase hx)
  calc g a + ∑ x ∈ univ.erase a, g x
      ≤ g a + (∑ x ∈ univ.erase a, f x + (Fintype.card α - 1) • c) := by gcongr
    _ = g a + (Fintype.card α - 1) • c + ∑ x ∈ univ.erase a, f x := by ac_rfl
    _ < f a + ∑ x ∈ univ.erase a, f x := add_lt_add_of_lt_of_le ha le_rfl

end Ordered

end Fintype
