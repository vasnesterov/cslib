/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SelfStabilization.StoneAge
public import Mathlib.Data.ZMod.Defs

/-!
# The asynchronous unison (AU) task and self-stabilization

Asynchronous unison (Couvreur–Francez–Gouda 1992; a.k.a. distributed pulse): every node outputs a
clock value in a cyclic group `ZMod m`;
* **safety**: neighbours' clock values differ by at most one (cyclically);
* **liveness**: for every (post-stabilization) time `t` and `i > 0`, each node updates its clock at
  least `i` times during `[t, ϱ^{d+i}(t))`, where `d` is the diameter (or a bound on it);
  updates are `+1` operations only.

An algorithm whose output map is `out : Q → Option (ZMod m)` (`none` on non-output states)
*stabilizes to AU by time `T`* (`AUFrom`) if from `T` on all nodes are in output states and the
output sequence satisfies safety, `+1`-monotonicity and liveness. Diameter bounds are expressed
with Mathlib's `SimpleGraph.ediam` (`G.ediam ≤ d`).

## Main definitions

* `StoneAge.AUFrom`: the execution solves AU from time `T`.
-/

@[expose] public section

namespace Cslib.StoneAge

variable {V Q : Type*} {m : ℕ}

/-- The execution `C` (under schedule `A`, on graph `G`) solves asynchronous unison with clock
values `out` from time `T` on, with liveness parameter `d` (a diameter bound). -/
structure AUFrom (G : SimpleGraph V) (A : ℕ → Set V) (out : Q → Option (ZMod m))
    (C : ℕ → V → Q) (d T : ℕ) : Prop where
  /-- All nodes are in output states. -/
  output : ∀ t, T ≤ t → ∀ v, (out (C t v)).isSome
  /-- Safety: neighbours' clocks differ by at most one. -/
  safety : ∀ t, T ≤ t → ∀ u v, G.Adj u v → ∀ c c', out (C t u) = some c → out (C t v) = some c' →
    c' = c - 1 ∨ c' = c ∨ c' = c + 1
  /-- Clocks are only updated by `+1` operations. -/
  incr : ∀ t, T ≤ t → ∀ v c c', out (C t v) = some c → out (C (t + 1) v) = some c' →
    c' = c ∨ c' = c + 1
  /-- Liveness: at least `i` clock updates of every node in `[t, ϱ^{d+i}(t))`. -/
  liveness : ∀ t, T ≤ t → ∀ v i, i ≤ ((Finset.Ico t ((rho A)^[d + i] t)).filter
    (fun s => out (C (s + 1) v) ≠ out (C s v))).card

end Cslib.StoneAge
