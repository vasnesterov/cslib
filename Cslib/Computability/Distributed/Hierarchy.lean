/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Quorum

/-! # Hierarchies of committees

A *hierarchy* over processes `P` is a finite rooted tree of committees: a leaf is a single process,
and an internal committee is split into an ordered family of children. Recursive Byzantine
agreement protocols run a protocol inside every committee, with the committee's members as
processes and `Quorum.tOf m` as the resilience of a committee of `m` members; children are used
as subroutines (e.g. as kings) of their parent.

## Main definitions

* `Hierarchy P`: `leaf p` or `node k ch` with children `ch : Fin k → Hierarchy P`.
* `Hierarchy.members`: the processes of a committee (the leaves below it).
* `Hierarchy.WF`: every internal committee has at least two children with pairwise disjoint
  members, so the children partition their parent.
* `Hierarchy.size`, `Hierarchy.branching`, `Hierarchy.depth`: `m_C`, `k_C`, and the number of
  internal levels on a longest root-to-leaf path.
* `Hierarchy.path`: the committees containing a process, root first; its `ℓ`-th entry is the
  committee of level `ℓ` containing the process.
* `Hierarchy.Good`: at most `tOf m_C` of the `m_C` members of `C` are faulty.

## Main statements

* `Hierarchy.WF.exists_good_child` (Fact G, from `Hierarchy.Good.exists_child`): a good internal
  committee has a good child, by averaging (`Quorum.exists_card_inter_le_tOf`).
* `Hierarchy.Good.exists_mem_notMem`: a good nonempty committee has a correct member.
* `Hierarchy.members_subset_members_node`, `Hierarchy.WF.members_ssubset`: children are proper
  subcommittees of their parent.
* `Hierarchy.WF.three_mul_tOf_lt`: a committee tolerates `tOf m_C` faults among its members,
  `3 * tOf m_C < Fintype.card ↥C.members`.
* `Hierarchy.WF.path_node`: the path of a process descends into the child containing it.
* `Hierarchy.WF.sum_card_inter_le`: the children of a well-formed committee have disjoint faulty
  members, `∑ i, #(F ∩ (ch i).members) ≤ #F`.
-/

@[expose] public section

namespace Cslib.Distributed

/-- A hierarchy of committees over processes `P`: a single process (`leaf p`), or a committee split
into an ordered family of `k` subcommittees (`node k ch`). Well-formedness (`Hierarchy.WF`) is a
separate predicate. -/
inductive Hierarchy (P : Type*) where
  /-- A committee consisting of the single process `p`. -/
  | leaf (p : P)
  /-- A committee with children `ch 0, …, ch (k - 1)`; its members are theirs. -/
  | node (k : ℕ) (ch : Fin k → Hierarchy P)

namespace Hierarchy

open Finset Quorum

variable {P : Type*}

/-! ### Shape -/

/-- The branching `k_C` of a committee: its number of children (`0` for a leaf). -/
def branching : Hierarchy P → ℕ
  | leaf _ => 0
  | node k _ => k

/-- The depth of a hierarchy: the number of internal committees on a longest root-to-leaf path
(`0` for a leaf). -/
def depth : Hierarchy P → ℕ
  | leaf _ => 0
  | node _ ch => (univ.sup fun i => depth (ch i)) + 1

@[simp] theorem branching_leaf (p : P) : (leaf p).branching = 0 := rfl

@[simp] theorem branching_node (k : ℕ) (ch : Fin k → Hierarchy P) : (node k ch).branching = k :=
  rfl

@[simp] theorem depth_leaf (p : P) : (leaf p).depth = 0 := rfl

theorem depth_node (k : ℕ) (ch : Fin k → Hierarchy P) :
    (node k ch).depth = (univ.sup fun i => (ch i).depth) + 1 := rfl

/-- A child is strictly shallower than its parent. -/
theorem depth_lt_depth_node {k : ℕ} (ch : Fin k → Hierarchy P) (i : Fin k) :
    (ch i).depth < (node k ch).depth :=
  Nat.lt_succ_of_le (le_sup (f := fun i => (ch i).depth) (mem_univ i))

/-! ### Members -/

variable [DecidableEq P]

/-- The members of a committee: the processes at the leaves below it. -/
def members : Hierarchy P → Finset P
  | leaf p => {p}
  | node _ ch => univ.biUnion fun i => members (ch i)

/-- The size `m_C = #C.members` of a committee. -/
abbrev size (X : Hierarchy P) : ℕ := #X.members

@[simp] theorem members_leaf (p : P) : (leaf p).members = {p} := rfl

@[simp] theorem size_leaf (p : P) : (leaf p).size = 1 := card_singleton p

theorem members_node (k : ℕ) (ch : Fin k → Hierarchy P) :
    (node k ch).members = univ.biUnion fun i => (ch i).members := rfl

@[simp] theorem mem_members_node {k : ℕ} {ch : Fin k → Hierarchy P} {p : P} :
    p ∈ (node k ch).members ↔ ∃ i, p ∈ (ch i).members := by
  simp [members_node]

/-- The members of a child are members of its parent (e.g. to embed a protocol over
`↥(ch i).members` into one over `↥(node k ch).members`). -/
theorem members_subset_members_node {k : ℕ} (ch : Fin k → Hierarchy P) (i : Fin k) :
    (ch i).members ⊆ (node k ch).members :=
  subset_biUnion_of_mem (fun i => (ch i).members) (mem_univ i)

/-! ### Well-formedness -/

/-- A hierarchy is well formed if every internal committee has at least two children, and the
members of its children are pairwise disjoint (so the children partition the committee). Leaves
are singletons, so every committee of a well-formed hierarchy is nonempty
(`Hierarchy.WF.members_nonempty`) and every child is a proper subcommittee
(`Hierarchy.WF.members_ssubset`). -/
def WF : Hierarchy P → Prop
  | leaf _ => True
  | node k ch =>
    2 ≤ k ∧ (Pairwise fun i j => Disjoint (ch i).members (ch j).members) ∧ ∀ i, (ch i).WF

@[simp] theorem wf_leaf (p : P) : (leaf p).WF := trivial

theorem wf_node_iff {k : ℕ} {ch : Fin k → Hierarchy P} :
    (node k ch).WF ↔
      2 ≤ k ∧ (Pairwise fun i j => Disjoint (ch i).members (ch j).members) ∧ ∀ i, (ch i).WF :=
  Iff.rfl

namespace WF

variable {k : ℕ} {ch : Fin k → Hierarchy P}

/-- A well-formed internal committee has at least two children. -/
theorem two_le (h : (node k ch).WF) : 2 ≤ k := h.1

/-- The children of a well-formed committee have pairwise disjoint members. -/
theorem disjoint (h : (node k ch).WF) :
    Pairwise fun i j => Disjoint (ch i).members (ch j).members :=
  h.2.1

/-- The children of a well-formed committee are well formed. -/
theorem child (h : (node k ch).WF) (i : Fin k) : (ch i).WF := h.2.2 i

/-- Every committee of a well-formed hierarchy is nonempty. -/
theorem members_nonempty {X : Hierarchy P} (h : X.WF) : X.members.Nonempty := by
  induction X with
  | leaf p => exact singleton_nonempty p
  | node k ch ih =>
    obtain ⟨p, hp⟩ := ih ⟨0, by have := h.two_le; omega⟩ (h.child _)
    exact ⟨p, mem_members_node.2 ⟨_, hp⟩⟩

/-- Every committee of a well-formed hierarchy has a positive size. -/
theorem size_pos {X : Hierarchy P} (h : X.WF) : 0 < X.size := h.members_nonempty.card_pos

/-- A committee of a well-formed hierarchy tolerates `tOf m_C` faults among its members: the
hypothesis `3 * t < Fintype.card P` of a protocol run inside the committee (over `↥X.members`,
with `t := tOf X.size`). -/
theorem three_mul_tOf_lt {X : Hierarchy P} (h : X.WF) :
    3 * tOf X.size < Fintype.card ↥X.members := by
  rw [Fintype.card_coe]
  exact Quorum.three_mul_tOf_lt h.size_pos

/-- In a well-formed committee, a member belongs to exactly one child. -/
theorem eq_of_mem_members (h : (node k ch).WF) {p : P} {i j : Fin k}
    (hi : p ∈ (ch i).members) (hj : p ∈ (ch j).members) : i = j := by
  by_contra hij
  exact disjoint_left.1 (h.disjoint hij) hi hj

/-- The children of a well-formed committee are disjoint, so the numbers of their members in a
set `F` (e.g. their faulty members) add up to at most `#F`. -/
theorem sum_card_inter_le (h : (node k ch).WF) (F : Finset P) :
    ∑ i, #(F ∩ (ch i).members) ≤ #F := by
  rw [← card_biUnion fun i _ j _ hij =>
    Disjoint.mono inter_subset_right inter_subset_right (h.disjoint hij)]
  exact card_le_card (biUnion_subset.2 fun i _ => inter_subset_left)

/-- A child of a well-formed committee is a proper subcommittee. -/
theorem members_ssubset (h : (node k ch).WF) (i : Fin k) :
    (ch i).members ⊂ (node k ch).members := by
  refine Finset.ssubset_iff_subset_ne.2 ⟨members_subset_members_node ch i, fun heq => ?_⟩
  have := Fin.nontrivial_iff_two_le.2 h.two_le
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨p, hp⟩ := (h.child j).members_nonempty
  exact hji (h.eq_of_mem_members hp (heq ▸ members_subset_members_node ch j hp))

end WF

/-! ### Paths: the committees containing a process -/

/-- The committees of `X` containing `p`, from the root `X` down to the leaf `leaf p`; empty if
`p` is not a member of `X`. The `ℓ`-th entry of `X.path p` is the committee of level `ℓ`
containing `p` (`C_ℓ(p)`), so sums over the levels of `p` are sums over `X.path p` (e.g. with
`List.zipIdx`). At an internal committee, the path descends into the first child containing `p`
(the only one if `X` is well formed, `Hierarchy.WF.path_node`). -/
def path : Hierarchy P → P → List (Hierarchy P)
  | leaf q, p => if p = q then [leaf q] else []
  | node k ch, p =>
    match (List.finRange k).find? fun i => p ∈ (ch i).members with
    | some i => node k ch :: path (ch i) p
    | none => []

theorem path_leaf (q p : P) : (leaf q).path p = if p = q then [leaf q] else [] := rfl

/-- A process outside `X` has an empty path. -/
theorem path_eq_nil {X : Hierarchy P} {p : P} (hp : p ∉ X.members) : X.path p = [] := by
  cases X with
  | leaf q => simp_all [path_leaf]
  | node k ch =>
    rw [path]
    split
    · next i hi =>
      exact absurd (mem_members_node.2 ⟨i, by simpa using List.find?_some hi⟩) hp
    · rfl

/-- The path of a member of a well-formed internal committee descends into the child containing
it. -/
theorem WF.path_node {k : ℕ} {ch : Fin k → Hierarchy P} (h : (node k ch).WF) {p : P} {i : Fin k}
    (hp : p ∈ (ch i).members) : (node k ch).path p = node k ch :: (ch i).path p := by
  rw [path]
  split
  · next j hj =>
    have hj' : p ∈ (ch j).members := by simpa using List.find?_some hj
    rw [h.eq_of_mem_members hj' hp]
  · next hn =>
    simp only [List.find?_eq_none, List.mem_finRange, decide_eq_true_eq, true_implies] at hn
    exact absurd hp (hn i)

/-- Every committee on the path of `p` contains `p`. -/
theorem mem_members_of_mem_path {X C : Hierarchy P} {p : P} (hC : C ∈ X.path p) :
    p ∈ C.members := by
  induction X with
  | leaf q =>
    rw [path_leaf] at hC
    split_ifs at hC with hpq
    · simp_all
    · simp at hC
  | node k ch ih =>
    rw [path] at hC
    split at hC
    · next i hi =>
      rcases List.mem_cons.1 hC with rfl | hC
      · exact mem_members_node.2 ⟨i, by simpa using List.find?_some hi⟩
      · exact ih i hC
    · simp at hC

/-- A path has at most `depth + 1` committees, one per level. -/
theorem length_path_le (X : Hierarchy P) (p : P) : (X.path p).length ≤ X.depth + 1 := by
  induction X with
  | leaf q =>
    rw [path_leaf]
    split_ifs <;> simp
  | node k ch ih =>
    rw [path]
    split
    · next i _ =>
      have := depth_lt_depth_node ch i
      simp only [List.length_cons]
      have := ih i
      omega
    · simp

/-! ### Good committees -/

/-- A committee `X` is *good* for the faulty processes `F` if at most `tOf m_X` of its `m_X`
members are faulty, i.e. if protocols run inside `X` with resilience `tOf m_X` meet their fault
assumption. A singleton is good iff its process is correct. -/
def Good (X : Hierarchy P) (F : Finset P) : Prop := #(F ∩ X.members) ≤ tOf X.size

instance (X : Hierarchy P) (F : Finset P) : Decidable (X.Good F) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem good_iff_card_le {X : Hierarchy P} {F : Finset P} :
    X.Good F ↔ #(F ∩ X.members) ≤ tOf X.size := Iff.rfl

/-- A nonempty committee is good iff fewer than a third of its members are faulty. -/
theorem good_iff {X : Hierarchy P} {F : Finset P} (hX : X.members.Nonempty) :
    X.Good F ↔ 3 * #(F ∩ X.members) < X.size :=
  le_tOf_iff hX.card_pos

/-- A committee is good if at most `t` of its members are faulty, where `3 * t < m_X` (e.g. the
root, all of whose members are processes, if at most `t < n / 3` processes are faulty). -/
theorem good_of_card_le {X : Hierarchy P} {F : Finset P} {t : ℕ} (hF : #(F ∩ X.members) ≤ t)
    (ht : 3 * t < X.size) : X.Good F :=
  hF.trans ((le_tOf_iff (by omega)).2 ht)

/-- A singleton is good iff its process is correct. -/
@[simp] theorem good_leaf {F : Finset P} {p : P} : (leaf p).Good F ↔ p ∉ F := by
  by_cases hp : p ∈ F <;> simp [good_iff_card_le, hp, tOf]

/-- A good nonempty committee has a correct member. -/
theorem Good.exists_mem_notMem {X : Hierarchy P} {F : Finset P} (hg : X.Good F)
    (hX : X.members.Nonempty) : ∃ p ∈ X.members, p ∉ F := by
  have := three_mul_tOf_lt (m := X.size) hX.card_pos
  obtain ⟨p, hp, hpF⟩ := Quorum.exists_notMem_of_lt_card (S := X.members) hg
    (show tOf X.size < X.size by omega)
  exact ⟨p, hp, fun hpF' => hpF (mem_inter.2 ⟨hpF', hp⟩)⟩

/-- **Fact G** (averaging): if a committee with at least one child, whose children have pairwise
disjoint members, is good, then one of its children is good: if all children were bad, the
committee would contain at least `∑ i, ⌈m_i / 3⌉ ≥ ⌈m / 3⌉` faulty members. -/
theorem Good.exists_child {k : ℕ} {ch : Fin k → Hierarchy P} {F : Finset P} (hk : 0 < k)
    (hd : Pairwise fun i j => Disjoint (ch i).members (ch j).members) (hg : (node k ch).Good F) :
    ∃ i, (ch i).Good F := by
  obtain ⟨i, -, hi⟩ := exists_card_inter_le_tOf (X := univ) (S := fun i => (ch i).members)
    ⟨⟨0, hk⟩, mem_univ _⟩ (hd.set_pairwise _) hg
  exact ⟨i, hi⟩

/-- **Fact G**: a good committee of a well-formed hierarchy has a good child. -/
theorem WF.exists_good_child {k : ℕ} {ch : Fin k → Hierarchy P} {F : Finset P}
    (h : (node k ch).WF) (hg : (node k ch).Good F) : ∃ i, (ch i).Good F :=
  hg.exists_child (by have := h.two_le; omega) h.disjoint

end Hierarchy

end Cslib.Distributed
