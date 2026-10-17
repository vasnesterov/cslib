/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Fintype.Card

/-!
# A third element

Impossibility proofs constantly pick "a process different from `p` and `q`" among at least three
processes. Mathlib has the one-point version (`Finset.exists_mem_ne`,
`Fintype.exists_ne_of_one_lt_card`) and the cardinal/`ENat.card` version
(`ENat.exists_ne_ne_of_three_le`); these are the `Finset`/`Fintype` forms of the latter.

## Main statements

* `Finset.exists_mem_ne_ne`: a finset with more than two elements has a member different from any
  two given elements;
* `Fintype.exists_ne_ne_of_two_lt_card`: the same in a finite type with more than two elements.
-/

@[expose] public section

namespace Finset

variable {α : Type*}

/-- A finset with more than two elements has a member different from any two given elements. -/
theorem exists_mem_ne_ne {s : Finset α} (h : 2 < #s) (a b : α) : ∃ c ∈ s, c ≠ a ∧ c ≠ b := by
  classical
  obtain ⟨c, hc, hab⟩ :=
    exists_mem_notMem_of_card_lt_card ((card_le_two (a := a) (b := b)).trans_lt h)
  simp only [mem_insert, mem_singleton, not_or] at hab
  exact ⟨c, hc, hab⟩

end Finset

namespace Fintype

variable {α : Type*} [Fintype α]

/-- A finite type with more than two elements has an element different from any two given
elements. -/
theorem exists_ne_ne_of_two_lt_card (h : 2 < card α) (a b : α) : ∃ c, c ≠ a ∧ c ≠ b := by
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_ne_ne (s := Finset.univ) h a b
  exact ⟨c, hc⟩

end Fintype
