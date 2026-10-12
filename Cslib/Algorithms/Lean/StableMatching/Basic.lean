/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fin.Basic

/-! # Stable matchings

We model a two-sided matching market with sides `L` ("proposers") and `R` ("receivers").
Strict preferences are given by injective rank functions (`Prefs`): lower rank means more
preferred. A perfect matching is an equivalence `μ : L ≃ R`; it is *stable* if no pair `(l, r)`
blocks it, i.e. there is no pair that strictly prefers each other to their partners
[GaleShapley1962].

## Main definitions

* `StableMatching.Prefs`: strict preferences of both sides as injective rank functions.
* `StableMatching.Prefs.ofPerms`: preferences given as permutations of `Fin k` (list format).
* `StableMatching.Prefs.Blocks`, `StableMatching.Prefs.IsStable`: blocking pairs and stability.

## Main results

* `StableMatching.Prefs.IsStable.apply_eq_of_mutual_best`: mutual first choices are matched in
  every stable matching.

## References

* [D. Gale, L. S. Shapley, *College Admissions and the Stability of Marriage*][GaleShapley1962]
-/

@[expose] public section

namespace Cslib.StableMatching

/-- Strict preferences of both sides, given as rank functions: lower rank = more preferred. -/
structure Prefs (L R : Type*) where
  /-- `rankL l r`: rank of `r` in the preference list of `l` (lower = better). -/
  rankL : L → R → ℕ
  /-- `rankR r l`: rank of `l` in the preference list of `r` (lower = better). -/
  rankR : R → L → ℕ
  /-- Preferences of the proposers are strict. -/
  injL : ∀ l, Function.Injective (rankL l)
  /-- Preferences of the receivers are strict. -/
  injR : ∀ r, Function.Injective (rankR r)

namespace Prefs

variable {L R : Type*}

/-- `(l, r)` blocks the perfect matching `μ : L ≃ R`: both strictly prefer each other to their
partners. -/
def Blocks (p : Prefs L R) (μ : L ≃ R) (l : L) (r : R) : Prop :=
  p.rankL l r < p.rankL l (μ l) ∧ p.rankR r l < p.rankR r (μ.symm r)

/-- A perfect matching is stable if it has no blocking pair. -/
def IsStable (p : Prefs L R) (μ : L ≃ R) : Prop := ∀ l r, ¬ p.Blocks μ l r

/-- If `l` and `r` are each other's first choices, then every stable matching matches them. -/
theorem IsStable.apply_eq_of_mutual_best {p : Prefs L R} {μ : L ≃ R} (hμ : p.IsStable μ)
    {l : L} {r : R} (hl : ∀ r', p.rankL l r ≤ p.rankL l r')
    (hr : ∀ l', p.rankR r l ≤ p.rankR r l') : μ l = r := by
  by_contra hne
  refine hμ l r ⟨lt_of_le_of_ne (hl _) fun e => hne (p.injL l e).symm,
    lt_of_le_of_ne (hr _) fun e => hne ?_⟩
  rw [p.injR r e, Equiv.apply_symm_apply]

/-- Preferences given as permutations of `Fin k`: the list of `l` is
`πL l 0, πL l 1, …, πL l (k-1)` (most preferred first), and similarly for `πR`. -/
def ofPerms {k : ℕ} (πL πR : Fin k → Equiv.Perm (Fin k)) : Prefs (Fin k) (Fin k) where
  rankL l r := ((πL l).symm r : ℕ)
  rankR r l := ((πR r).symm l : ℕ)
  injL l := Fin.val_injective.comp (πL l).symm.injective
  injR r := Fin.val_injective.comp (πR r).symm.injective

@[simp]
theorem ofPerms_rankL {k : ℕ} (πL πR : Fin k → Equiv.Perm (Fin k)) (l r : Fin k) :
    (ofPerms πL πR).rankL l r = ((πL l).symm r : ℕ) := rfl

@[simp]
theorem ofPerms_rankR {k : ℕ} (πL πR : Fin k → Equiv.Perm (Fin k)) (r l : Fin k) :
    (ofPerms πL πR).rankR r l = ((πR r).symm l : ℕ) := rfl

/-- With list preferences: mutual first choices are matched in every stable matching. -/
theorem IsStable.ofPerms_apply_eq {k : ℕ} [NeZero k] {πL πR : Fin k → Equiv.Perm (Fin k)}
    {μ : Fin k ≃ Fin k} (hμ : (ofPerms πL πR).IsStable μ) {l r : Fin k}
    (hl : πL l 0 = r) (hr : πR r 0 = l) : μ l = r :=
  hμ.apply_eq_of_mutual_best (fun _ => by simp [← hl]) (fun _ => by simp [← hr])

end Prefs

end Cslib.StableMatching
