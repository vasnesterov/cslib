/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Foundations.Combinatorics.SimpleGraph.RootedTree
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Basic.Real.Basic

/-!
# Low-congestion shortcuts

Definitions following Ghaffari–Haeupler (SODA'16, PODC'21) and Haeupler–Izumi–Zuzic (PODC'16).

A *collection of parts* of a graph `G` is a family `P : ι → Finset V` of pairwise disjoint vertex
sets, each inducing a connected subgraph of `G`. A *shortcut* assigns to every part `P i` a set of
edges `H i ⊆ E(G)`.

* **congestion**: every edge of `G` lies in at most `c` of the sets `H i` (`CongestionLE`);
* **dilation**: the graph `G[P i] + H i` (`partGraph`) has diameter at most `d` on its vertex set
  `P i ∪ V(H i)` (`DilationLE`);
* **tree-restricted**: all `H i` consist of edges of a rooted spanning tree `T`;
* **blocks**: the connected components of the graph `(P i ∪ V(H i), H i)` (`numBlocks`).

`AdmitsTreeShortcuts` / `AdmitsPartialTreeShortcuts` are Definitions 2.4 / 2.5 of Ghaffari–Haeupler
(PODC'21), with the additional requirement that every block of a part contains a vertex of that
part (`BlocksMeetPart`); see the paper's `differencies.md` for why this is needed.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A collection of parts: pairwise disjoint vertex sets, each inducing a connected subgraph
(in particular each part is nonempty). -/
structure IsParts {ι : Type*} (P : ι → Finset V) : Prop where
  disjoint : Pairwise fun i j => Disjoint (P i) (P j)
  connected : ∀ i, (G.induce (P i : Set V)).Connected

variable {G}

/-- The vertex set `P ∪ V(H)` of a part together with its shortcut edges. -/
def partVerts (P : Finset V) (H : Finset (Sym2 V)) : Set V :=
  (P : Set V) ∪ {v | ∃ e ∈ H, v ∈ e}

variable (G) in
/-- The graph `G[P] + H`: edges of `G` inside `P`, plus the shortcut edges `H` (which are assumed
to be edges of `G`). -/
def partGraph (P : Finset V) (H : Finset (Sym2 V)) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ((x ∈ P ∧ y ∈ P) ∨ s(x, y) ∈ H)
  symm := ⟨fun x y ⟨h, h'⟩ => ⟨h.symm, by
    rcases h' with ⟨a, b⟩ | h'
    · exact Or.inl ⟨b, a⟩
    · exact Or.inr (by rwa [Sym2.eq_swap])⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

/-- The graph `(V, H)` whose components (restricted to `partVerts P H`) are the blocks. -/
abbrev blockGraph (H : Finset (Sym2 V)) : SimpleGraph V := fromEdgeSet (H : Set (Sym2 V))

/-- The number of blocks of a part `P` with shortcut edges `H`: the number of connected components
of the graph `(P ∪ V(H), H)`. -/
noncomputable def numBlocks (P : Finset V) (H : Finset (Sym2 V)) : ℕ :=
  ((blockGraph H).connectedComponentMk '' partVerts P H).ncard

/-- Every block contains a vertex of the part. -/
def BlocksMeetPart (P : Finset V) (H : Finset (Sym2 V)) : Prop :=
  ∀ x ∈ partVerts P H, ∃ y ∈ P, (blockGraph H).Reachable x y

variable (G) in
/-- Dilation at most `d`: the graph `G[P] + H` has diameter at most `d` on its vertex set
`P ∪ V(H)` (any two of these vertices are connected by a path of length at most `d`). -/
def DilationLE (P : Finset V) (H : Finset (Sym2 V)) (d : ℝ) : Prop :=
  ∀ x ∈ partVerts P H, ∀ y ∈ partVerts P H,
    (partGraph G P H).Reachable x y ∧ ((partGraph G P H).dist x y : ℝ) ≤ d

variable (G) in
/-- Congestion at most `c` for the parts in `J`: every edge of `G` lies in at most `c` of the sets
`H i`, `i ∈ J`. -/
def CongestionLE {ι : Type*} [DecidableEq V] (J : Finset ι) (H : ι → Finset (Sym2 V)) (c : ℝ) :
    Prop :=
  ∀ e ∈ G.edgeSet, ((J.filter fun i => e ∈ H i).card : ℝ) ≤ c

/-- Definition 2.4 of Ghaffari–Haeupler (PODC'21): `G` admits tree-restricted `c`-congestion
`b`-block shortcuts for trees of depth `≤ D`: for every rooted spanning tree `T` of depth `≤ D` and
every collection of parts there is a `T`-restricted shortcut with congestion `≤ c` in which every
part has at most `b` blocks (each block containing a vertex of the part). -/
def AdmitsTreeShortcuts [DecidableEq V] (G : SimpleGraph V) (D : ℕ) (c b : ℝ) : Prop :=
  ∀ T : G.RootedTree, T.DepthLE D → ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset V),
    G.IsParts P → ∃ H : ι → Finset (Sym2 V), (∀ i, T.Restricts (H i)) ∧
      G.CongestionLE Finset.univ H c ∧ ∀ i, (numBlocks (P i) (H i) : ℝ) ≤ b ∧
        BlocksMeetPart (P i) (H i)

/-- Definition 2.5 of Ghaffari–Haeupler (PODC'21): `G` admits tree-restricted `c`-congestion
`b`-block *partial* shortcuts for trees of depth `≤ D`: for every rooted spanning tree `T` of
depth `≤ D` and every collection of `k` parts, at least `k / 2` of the parts have a `T`-restricted
shortcut with congestion `≤ c` (among themselves) and at most `b` blocks per part. -/
def AdmitsPartialTreeShortcuts [DecidableEq V] (G : SimpleGraph V) (D : ℕ) (c b : ℝ) : Prop :=
  ∀ T : G.RootedTree, T.DepthLE D → ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset V),
    G.IsParts P → ∃ J : Finset ι, Fintype.card ι ≤ 2 * J.card ∧
      ∃ H : ι → Finset (Sym2 V), (∀ i ∈ J, T.Restricts (H i)) ∧ G.CongestionLE J H c ∧
        ∀ i ∈ J, (numBlocks (P i) (H i) : ℝ) ≤ b ∧ BlocksMeetPart (P i) (H i)

end SimpleGraph
