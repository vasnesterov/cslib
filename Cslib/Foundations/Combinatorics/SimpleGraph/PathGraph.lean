/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Decidable adjacency in the path graph

Mathlib's `SimpleGraph.pathGraph n` on `Fin n` comes without a `DecidableRel` instance for its
adjacency, which is needed to compute degrees and edge sets. Adjacency is decided through
`SimpleGraph.pathGraph_adj` (consecutive values).
-/

@[expose] public section

namespace SimpleGraph

/-- Adjacency in `pathGraph n` is decidable: it means having consecutive values. -/
instance decidableAdjPathGraph (n : ℕ) : DecidableRel (pathGraph n).Adj := fun _ _ =>
  decidable_of_iff _ pathGraph_adj.symm

end SimpleGraph
