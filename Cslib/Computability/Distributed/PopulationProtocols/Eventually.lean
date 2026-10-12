/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin

/-! # "Eventually forever" for finitely many agents

If every agent eventually satisfies a property which, once true (after time `T0`), stays true, then
from some time on all agents satisfy it. This is the typical way to combine per-agent convergence
statements into a statement about whole configurations.
-/

@[expose] public section

namespace Cslib.PopulationProtocol

/-- If, after time `T0`, the property `P t x` persists for every agent `x`, and every agent
eventually satisfies it, then from some time `T ≥ T0` on all agents satisfy it. -/
lemma eventually_all {A : Type*} [Finite A] {P : ℕ → A → Prop} (T0 : ℕ)
    (hpers : ∀ t ≥ T0, ∀ x, P t x → P (t + 1) x) (hev : ∀ x, ∃ t ≥ T0, P t x) :
    ∃ T ≥ T0, ∀ t ≥ T, ∀ x, P t x := by
  classical
  have := Fintype.ofFinite A
  choose tx htx hP using hev
  have key : ∀ x, ∀ t ≥ tx x, P t x := by
    intro x t hle
    induction t, hle using Nat.le_induction with
    | base => exact hP x
    | succ t h ih => exact hpers t (le_trans (htx x) h) x ih
  refine ⟨T0 ⊔ Finset.univ.sup tx, le_sup_left, fun t ht x => key x t ?_⟩
  exact le_trans (Finset.le_sup (f := tx) (Finset.mem_univ x)) (le_trans le_sup_right ht)

end Cslib.PopulationProtocol
