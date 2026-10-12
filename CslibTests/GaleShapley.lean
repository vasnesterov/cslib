/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Cslib.Algorithms.Lean.StableMatching.GaleShapley
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Group.End

/-! # Tests for the Gale–Shapley algorithm -/

namespace CslibTests.GaleShapley

open Cslib.StableMatching

/- Lists: proposers `0: [1,0,2]`, `1: [0,1,2]`, `2: [1,2,0]`;
receivers `0: [0,1,2]`, `1: [2,1,0]`, `2: [1,2,0]`. Hand-run Gale–Shapley gives `0↦0, 1↦2, 2↦1`. -/
/-- info: [0, 2, 1] -/
#guard_msgs in
#eval
  let πL : Fin 3 → Equiv.Perm (Fin 3) := ![Equiv.swap 0 1, 1, finRotate 3]
  let πR : Fin 3 → Equiv.Perm (Fin 3) := ![1, Equiv.swap 0 2, finRotate 3]
  List.ofFn fun i => (galeShapley (Prefs.ofPerms πL πR) rfl i : ℕ)

end CslibTests.GaleShapley
