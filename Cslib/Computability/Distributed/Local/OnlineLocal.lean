/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Logic.Equiv.Fintype

/-!
# The Online-LOCAL model (deterministic)

The Online-LOCAL model of Akbari, Eslami, Lievonen, Melnyk, Särkijärvi and Suomela (ICALP 2023),
as described in Chang–Mishra–Nguyen–Yang–Yeh (PODC 2024), §2.2:

* the input is a graph `H` whose nodes are the unique identifiers `ι` (an adversary chooses which
  identifier sits where; for a fixed host graph `G` on positions `V` this is a bijection
  `pos : ι ≃ V` and `H = G.comap pos`);
* the adversary reveals the nodes one by one in an order `σ = (v₁, …, vₙ)`;
* when `vᵢ` is revealed, the algorithm must output the label of `vᵢ`, as a function of the
  *view* `(H[B(v₁..vᵢ, T)], (v₁, …, vᵢ))`: the subgraph induced by the radius-`T` balls around all
  nodes revealed so far (with identifiers), and the sequence itself. This is the "global memory":
  everything seen so far may influence the output.

Deterministic algorithms are plain functions `View ι → L`; the locality `T` is a parameter of a run.
Since the algorithm is deterministic, an adaptive adversary is no stronger than an oblivious one:
a lower bound only has to exhibit one pair `(H, σ)` on which the produced labelling is wrong.

## Main definitions and results

* `ball G U k`: the closed `k`-neighbourhood of a set (defined by `k` one-step expansions;
  `mem_ball_iff_walk` relates it to walks).
* `View`, `view H T s`, `Algorithm`, `Algorithm.label A H T σ x`.
* `AgreeOn H₁ H₂ U T`: `H₁` and `H₂` agree on all edges seen from `U` with radius `T`.
  `label_eq_of_agreeOn`: then every revealed node gets the same label in both runs
  (*indistinguishability*); `label_append`: labels never change once given.
* `exists_move`: re-embedding a far-away part of the revealed region by a local isomorphism `ρ`
  (the adversary's power "to adjust how the current discovered region fits into `G`").
* `seeAll_properOn`, `seeAll_colors`: non-vacuity — if radius-`T` balls cover the whole
  (colourable) graph, a correct algorithm exists.

## References

* A. Akbari, N. Eslami, H. Lievonen, D. Melnyk, J. Särkijärvi, J. Suomela, *Locality in online,
  dynamic, sequential, and distributed graph algorithms*, ICALP 2023.
* Y.-J. Chang, G. Mishra, H. T. Nguyen, M. Yang, Y.-C. Yeh, *A tight lower bound for 3-coloring
  grids in the Online-LOCAL model*, PODC 2024.
-/

@[expose] public section

namespace Cslib.OnlineLocal

open SimpleGraph

variable {V ι L : Type*}

/-! ### Balls -/

/-- The closed `k`-neighbourhood `B(U, k)` of a set `U` of nodes. -/
def ball (G : SimpleGraph V) (U : Set V) : ℕ → Set V
  | 0 => U
  | k + 1 => ball G U k ∪ {y | ∃ x ∈ ball G U k, G.Adj x y}

section Ball

variable {G : SimpleGraph V} {U U' : Set V} {k l : ℕ}

@[simp] lemma ball_zero : ball G U 0 = U := rfl

lemma ball_succ : ball G U (k + 1) = ball G U k ∪ {y | ∃ x ∈ ball G U k, G.Adj x y} := rfl

lemma ball_subset_succ : ball G U k ⊆ ball G U (k + 1) := Set.subset_union_left

lemma ball_mono (h : k ≤ l) : ball G U k ⊆ ball G U l := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans ball_subset_succ

lemma subset_ball : U ⊆ ball G U k := ball_mono (Nat.zero_le k)

lemma mem_ball_succ_of_adj {x y : V} (hx : x ∈ ball G U k) (h : G.Adj x y) :
    y ∈ ball G U (k + 1) := Or.inr ⟨x, hx, h⟩

lemma ball_mono_set (h : U ⊆ U') : ball G U k ⊆ ball G U' k := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rintro y (hy | ⟨x, hx, hxy⟩)
    · exact Or.inl (ih hy)
    · exact Or.inr ⟨x, ih hx, hxy⟩

lemma ball_union : ball G (U ∪ U') k = ball G U k ∪ ball G U' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    ext y
    simp only [ball_succ, ih, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ((h | h) | ⟨x, hx | hx, hxy⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr ⟨x, hx, hxy⟩)
      · exact Or.inr (Or.inr ⟨x, hx, hxy⟩)
    · rintro ((h | ⟨x, hx, hxy⟩) | (h | ⟨x, hx, hxy⟩))
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨x, Or.inl hx, hxy⟩
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨x, Or.inr hx, hxy⟩

lemma ball_add : ball G (ball G U k) l = ball G U (k + l) := by
  induction l with
  | zero => rfl
  | succ l ih => rw [ball_succ, ih, ← Nat.add_assoc, ball_succ]

lemma mem_ball_of_walk {u y : V} (p : G.Walk u y) (hu : u ∈ U) : y ∈ ball G U p.length := by
  induction p generalizing U with
  | nil => exact hu
  | cons h q ih =>
    have := ih (U := ball G U 1) (mem_ball_succ_of_adj hu h)
    rw [ball_add] at this
    simpa [Nat.add_comm] using this

/-- `y ∈ B(U, k)` iff some walk of length `≤ k` leads from `U` to `y`. -/
lemma mem_ball_iff_walk {y : V} :
    y ∈ ball G U k ↔ ∃ u ∈ U, ∃ p : G.Walk u y, p.length ≤ k := by
  induction k generalizing y with
  | zero =>
    constructor
    · intro hy; exact ⟨y, hy, .nil, le_rfl⟩
    · rintro ⟨u, hu, p, hp⟩
      cases p with
      | nil => exact hu
      | cons _ _ => simp at hp
  | succ k ih =>
    constructor
    · rintro (hy | ⟨x, hx, hxy⟩)
      · obtain ⟨u, hu, p, hp⟩ := ih.1 hy
        exact ⟨u, hu, p, by omega⟩
      · obtain ⟨u, hu, p, hp⟩ := ih.1 hx
        exact ⟨u, hu, p.concat hxy, by simp; omega⟩
    · rintro ⟨u, hu, p, hp⟩
      exact ball_mono hp (mem_ball_of_walk p hu)

/-- Balls are transported along isomorphic copies `G.comap e`. -/
lemma ball_comap_equiv {W : Type*} (G : SimpleGraph W) (e : V ≃ W) (U : Set V) (k : ℕ) :
    ball (G.comap e) U k = e ⁻¹' ball G (e '' U) k := by
  induction k with
  | zero => ext x; simp
  | succ k ih =>
    ext y
    simp only [ball_succ, ih, Set.preimage_union, Set.mem_union, Set.mem_preimage,
      Set.mem_ofPred_eq, comap_adj]
    constructor
    · rintro (h | ⟨x, hx, hxy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨e x, hx, hxy⟩
    · rintro (h | ⟨x, hx, hxy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨e.symm x, by simpa using hx, by simpa using hxy⟩

end Ball

/-! ### Views, algorithms, runs -/

/-- The graph `H` restricted to the node set `W` (edges with both ends in `W`), on the same
identifier type. -/
def restrict (H : SimpleGraph ι) (W : Set ι) : SimpleGraph ι where
  Adj x y := H.Adj x y ∧ x ∈ W ∧ y ∈ W
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => H.loopless.irrefl _ h.1⟩

/-- What an Online-LOCAL algorithm sees when a node is revealed: the node set of the discovered
region `B(v₁..vᵢ, T)`, the induced subgraph on it (with identifiers), and the sequence of revealed
nodes `[v₁, …, vᵢ]` (the newest one last). -/
@[ext]
structure View (ι : Type*) where
  /-- The discovered region `B({v₁, …, vᵢ}, T)`. -/
  verts : Set ι
  /-- The subgraph induced by the discovered region. -/
  graph : SimpleGraph ι
  /-- The revealed nodes, in order of revelation. -/
  seq : List ι

/-- The view after revealing the nodes of `s` (in this order) in the input graph `H` with
locality `T`. -/
def view (H : SimpleGraph ι) (T : ℕ) (s : List ι) : View ι :=
  ⟨ball H {x | x ∈ s} T, restrict H (ball H {x | x ∈ s} T), s⟩

/-- A deterministic Online-LOCAL algorithm with output labels `L`: it maps the current view to the
label of the most recently revealed node. -/
def Algorithm (ι L : Type*) := View ι → L

/-- The label that algorithm `A`, run with locality `T` on input `H` under the reveal order `σ`,
gives to the node `x` (the label computed when `x` is revealed). -/
def Algorithm.label [DecidableEq ι] (A : Algorithm ι L) (H : SimpleGraph ι) (T : ℕ)
    (σ : List ι) (x : ι) : L :=
  A (view H T (σ.take (σ.idxOf x + 1)))

/-- `σ` is a valid reveal order: every node is revealed exactly once. -/
def IsOrder (σ : List ι) : Prop := σ.Nodup ∧ ∀ x, x ∈ σ

/-- The run of `A` with locality `T` on `H` under `σ` produces a proper colouring. -/
def Algorithm.ProperOn [DecidableEq ι] (A : Algorithm ι L) (H : SimpleGraph ι) (T : ℕ)
    (σ : List ι) : Prop :=
  ∀ x y, H.Adj x y → A.label H T σ x ≠ A.label H T σ y

/-- `A` properly colours, with locality `T`, every input `H = G.comap pos` (every assignment `pos`
of the identifiers `ι` to the nodes of the host graph `G`) under every reveal order. -/
def Algorithm.Colors [DecidableEq ι] (A : Algorithm ι L) (G : SimpleGraph V) (T : ℕ) : Prop :=
  ∀ (pos : ι ≃ V) (σ : List ι), IsOrder σ → A.ProperOn (G.comap pos) T σ

/-- Extend a list of revealed nodes to a complete reveal order ("let the algorithm colour the
remaining nodes in some order"). -/
noncomputable def completeOrder [Fintype ι] [DecidableEq ι] (σ : List ι) : List ι :=
  σ ++ (Finset.univ : Finset ι).toList.filter (fun x => x ∉ σ)

lemma isOrder_completeOrder [Fintype ι] [DecidableEq ι] {σ : List ι} (h : σ.Nodup) :
    IsOrder (completeOrder σ) := by
  refine ⟨List.nodup_append.2 ⟨h, (Finset.nodup_toList _).filter _, ?_⟩, fun x => ?_⟩
  · intro x hx y hy hxy
    subst hxy
    simp only [List.mem_filter, decide_eq_true_eq] at hy
    exact hy.2 hx
  · by_cases hx : x ∈ σ
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_filter.2 ⟨by simp, by simpa using hx⟩)

section Run

variable [DecidableEq ι] (A : Algorithm ι L)

/-- Labels never change: revealing more nodes later does not affect the label of `x`. -/
lemma label_append (H : SimpleGraph ι) (T : ℕ) {σ : List ι} (τ : List ι) {x : ι} (hx : x ∈ σ) :
    A.label H T (σ ++ τ) x = A.label H T σ x := by
  unfold Algorithm.label
  rw [List.idxOf_append_of_mem hx, List.take_append_of_le_length]
  exact List.idxOf_lt_length_of_mem hx

end Run

/-! ### Indistinguishability -/

/-- `H₁` and `H₂` look the same from `U` with radius `T`: they agree on all edges at a node of
`B(U, T-1)` and on all edges inside `B(U, T)`. -/
structure AgreeOn (H₁ H₂ : SimpleGraph ι) (U : Set ι) (T : ℕ) : Prop where
  inner : ∀ k < T, ∀ x ∈ ball H₁ U k, ∀ y, H₁.Adj x y ↔ H₂.Adj x y
  outer : ∀ x ∈ ball H₁ U T, ∀ y ∈ ball H₁ U T, H₁.Adj x y ↔ H₂.Adj x y

namespace AgreeOn

variable {H₁ H₂ : SimpleGraph ι} {U U' : Set ι} {T : ℕ}

lemma ball_eq (h : AgreeOn H₁ H₂ U T) {k : ℕ} (hk : k ≤ T) : ball H₁ U k = ball H₂ U k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ih := ih (by omega)
    ext y
    simp only [ball_succ, ← ih, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (h' | ⟨x, hx, hxy⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨x, hx, (h.inner k (by omega) x hx y).1 hxy⟩
    · rintro (h' | ⟨x, hx, hxy⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨x, hx, (h.inner k (by omega) x hx y).2 hxy⟩

lemma mono (h : AgreeOn H₁ H₂ U T) (hU : U' ⊆ U) : AgreeOn H₁ H₂ U' T :=
  ⟨fun k hk x hx y => h.inner k hk x (ball_mono_set hU hx) y,
   fun x hx y hy => h.outer x (ball_mono_set hU hx) y (ball_mono_set hU hy)⟩

lemma trans {H₃ : SimpleGraph ι} (h₁ : AgreeOn H₁ H₂ U T) (h₂ : AgreeOn H₂ H₃ U T) :
    AgreeOn H₁ H₃ U T := by
  refine ⟨fun k hk x hx y => ?_, fun x hx y hy => ?_⟩
  · rw [h₁.inner k hk x hx y, h₂.inner k hk x (by rwa [← h₁.ball_eq hk.le]) y]
  · have e := h₁.ball_eq (le_refl T)
    rw [h₁.outer x hx y hy, h₂.outer x (e ▸ hx) y (e ▸ hy)]

lemma view_eq {s : List ι} (h : AgreeOn H₁ H₂ {x | x ∈ s} T) : view H₁ T s = view H₂ T s := by
  have e := h.ball_eq (le_refl T)
  ext x y
  · simp [view, e]
  · simp only [view, restrict, ← e]
    constructor
    · rintro ⟨hxy, hx, hy⟩; exact ⟨(h.outer x hx y hy).1 hxy, hx, hy⟩
    · rintro ⟨hxy, hx, hy⟩; exact ⟨(h.outer x hx y hy).2 hxy, hx, hy⟩
  · rfl

end AgreeOn

/-- **Indistinguishability.** If `H₁` and `H₂` agree around the revealed nodes, the algorithm gives
every revealed node the same label in both runs. -/
theorem label_eq_of_agreeOn [DecidableEq ι] (A : Algorithm ι L) {H₁ H₂ : SimpleGraph ι} {T : ℕ}
    {σ : List ι} (h : AgreeOn H₁ H₂ {x | x ∈ σ} T) (x : ι) :
    A.label H₁ T σ x = A.label H₂ T σ x := by
  unfold Algorithm.label
  congr 1
  exact (h.mono fun y hy => List.mem_of_mem_take hy).view_eq

/-! ### Moving parts of the discovered region (adversary re-embeddings) -/

section Move

variable {G : SimpleGraph V}

/-- `AgreeOn` for isomorphic copies reduces to the host graph. -/
lemma agreeOn_comap {W : Type*} {G : SimpleGraph W} (pos : ι ≃ W) (μ : Equiv.Perm W)
    {U : Set ι} {T : ℕ} (h : AgreeOn G (G.comap μ) (pos '' U) T) :
    AgreeOn (G.comap pos) (G.comap (pos.trans μ)) U T := by
  refine ⟨fun k hk x hx y => ?_, fun x hx y hy => ?_⟩
  · rw [ball_comap_equiv] at hx
    simpa using h.inner k hk (pos x) hx (pos y)
  · rw [ball_comap_equiv] at hx hy
    simpa using h.outer (pos x) hx (pos y) hy

/-- A permutation of positions fixing the whole radius-`T` ball pointwise is invisible. -/
lemma agreeOn_of_fix {U : Set V} {T : ℕ} (μ : Equiv.Perm V) (hμ : ∀ p ∈ ball G U T, μ p = p) :
    AgreeOn G (G.comap μ) U T := by
  refine ⟨fun k hk x hx y => ?_, fun x hx y hy => ?_⟩
  · have hxT : x ∈ ball G U T := ball_mono hk.le hx
    simp only [comap_adj, hμ x hxT]
    constructor
    · intro hxy
      rwa [hμ y (ball_mono (by omega) (mem_ball_succ_of_adj hx hxy))]
    · intro hxy
      have hy : μ y ∈ ball G U T := ball_mono (by omega) (mem_ball_succ_of_adj hx hxy)
      have : μ (μ y) = μ y := hμ _ hy
      rwa [μ.injective this] at hxy
  · simp [hμ x hx, hμ y hy]

/-- A function injective on a set of a finite type extends to a permutation. -/
lemma exists_perm_extend [Finite V] {S : Set V} {f : V → V} (hf : Set.InjOn f S) :
    ∃ μ : Equiv.Perm V, ∀ x ∈ S, μ x = f x := by
  classical
  let e : {x // x ∈ S} ≃ {x // x ∈ f '' S} := hf.bijOn_image.equiv f
  exact ⟨e.extendSubtype, fun x hx => by
    rw [Equiv.extendSubtype_apply_of_mem e x hx]; rfl⟩

/-- **Re-embedding a far-away part.** Let the revealed positions be `U₁ ∪ U₂`, with
`X = B(U₁,T)` and `Y = B(U₂,T)`. Suppose `ρ` maps `Y` isomorphically (as an induced subgraph) onto
a region whose inner part has all its neighbours inside `ρ '' Y`, and that neither `Y` nor `ρ '' Y`
meets or touches `X`. Then some permutation `μ` of the positions fixes `X`, acts as `ρ` on `Y`,
and is invisible to the algorithm. -/
theorem exists_move [Finite V] {U₁ U₂ : Set V} {T : ℕ} (ρ : V → V)
    (hinj : Set.InjOn ρ (ball G U₂ T))
    (hiso : ∀ p ∈ ball G U₂ T, ∀ q ∈ ball G U₂ T, G.Adj p q ↔ G.Adj (ρ p) (ρ q))
    (hnbr : ∀ k < T, ∀ p ∈ ball G U₂ k, ∀ q, G.Adj (ρ p) q → q ∈ ρ '' ball G U₂ T)
    (hsep : ∀ p ∈ ball G U₁ T, ∀ q ∈ ball G U₂ T,
      p ≠ q ∧ ¬ G.Adj p q ∧ p ≠ ρ q ∧ ¬ G.Adj p (ρ q)) :
    ∃ μ : Equiv.Perm V, (∀ p ∈ ball G U₁ T, μ p = p) ∧ (∀ p ∈ ball G U₂ T, μ p = ρ p) ∧
      AgreeOn G (G.comap μ) (U₁ ∪ U₂) T := by
  classical
  set X := ball G U₁ T
  set Y := ball G U₂ T
  let f : V → V := fun p => if p ∈ Y then ρ p else p
  have hfX : ∀ p ∈ X, f p = p := fun p hp => by
    have : p ∉ Y := fun hY => (hsep p hp p hY).1 rfl
    simp [f, this]
  have hfY : ∀ p ∈ Y, f p = ρ p := fun p hp => by simp [f, hp]
  have hf : Set.InjOn f (X ∪ Y) := by
    rintro p (hp | hp) q (hq | hq) hpq
    · rwa [hfX p hp, hfX q hq] at hpq
    · rw [hfX p hp, hfY q hq] at hpq; exact absurd hpq (hsep p hp q hq).2.2.1
    · rw [hfY p hp, hfX q hq] at hpq; exact absurd hpq.symm (hsep q hq p hp).2.2.1
    · rw [hfY p hp, hfY q hq] at hpq; exact hinj hp hq hpq
  obtain ⟨μ, hμ⟩ := exists_perm_extend hf
  have hμX : ∀ p ∈ X, μ p = p := fun p hp => (hμ p (Or.inl hp)).trans (hfX p hp)
  have hμY : ∀ p ∈ Y, μ p = ρ p := fun p hp => (hμ p (Or.inr hp)).trans (hfY p hp)
  refine ⟨μ, hμX, hμY, fun k hk x hx y => ?_, fun x hx y hy => ?_⟩
  · rw [ball_union] at hx
    have hk1 : k + 1 ≤ T := hk
    simp only [comap_adj]
    rcases hx with hx | hx
    · rw [hμX x (ball_mono hk.le hx)]
      constructor
      · intro hxy
        rwa [hμX y (ball_mono hk1 (mem_ball_succ_of_adj hx hxy))]
      · intro hxy
        have hy : μ y ∈ X := ball_mono hk1 (mem_ball_succ_of_adj hx hxy)
        have e : μ y = y := μ.injective (hμX _ hy)
        rwa [e] at hxy
    · rw [hμY x (ball_mono hk.le hx)]
      constructor
      · intro hxy
        have hy : y ∈ Y := ball_mono hk1 (mem_ball_succ_of_adj hx hxy)
        rw [hμY y hy]
        exact (hiso x (ball_mono hk.le hx) y hy).1 hxy
      · intro hxy
        obtain ⟨z, hz, hzy⟩ := hnbr k hk x hx (μ y) hxy
        rw [← hμY z hz] at hzy
        obtain rfl := μ.injective hzy
        rw [hμY z hz] at hxy
        exact (hiso x (ball_mono hk.le hx) z hz).2 hxy
  · rw [ball_union] at hx hy
    simp only [comap_adj]
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hμX x hx, hμX y hy]
    · rw [hμX x hx, hμY y hy]
      exact iff_of_false (hsep x hx y hy).2.1 (hsep x hx y hy).2.2.2
    · rw [hμY x hx, hμX y hy]
      exact iff_of_false (fun h => (hsep y hy x hx).2.1 h.symm)
        (fun h => (hsep y hy x hx).2.2.2 h.symm)
    · rw [hμY x hx, hμY y hy]; exact hiso x hx y hy

end Move

/-! ### Non-vacuity: large locality suffices -/

section NonVacuity

open Classical in
/-- The "see everything" algorithm: properly `c`-colour the whole discovered graph in a fixed
(choice-based) way, if possible, and output the colour of the newest node. -/
noncomputable def seeAll (L : Type*) [Inhabited L] : Algorithm ι L := fun v =>
  if h : ∃ χ : ι → L, ∀ x y, v.graph.Adj x y → χ x ≠ χ y then
    (v.seq.getLast?.map h.choose).getD default
  else default

/-- **Non-vacuity.** If every radius-`T` ball of `H` is the whole node set and `H` has a proper
`L`-colouring, then `seeAll` properly colours `H` under every reveal order. -/
theorem seeAll_properOn [DecidableEq ι] [Inhabited L] {H : SimpleGraph ι} {T : ℕ}
    (hball : ∀ x, ball H {x} T = Set.univ) (hcol : ∃ χ : ι → L, ∀ x y, H.Adj x y → χ x ≠ χ y)
    {σ : List ι} (hσ : IsOrder σ) : (seeAll (ι := ι) L).ProperOn H T σ := by
  classical
  -- every nonempty prefix sees the whole graph
  have hview : ∀ x ∈ σ, (view H T (σ.take (σ.idxOf x + 1))).graph = H ∧
      (view H T (σ.take (σ.idxOf x + 1))).seq.getLast? = some x := by
    intro x hx
    have hmem : x ∈ σ.take (σ.idxOf x + 1) := by
      rw [List.mem_take_iff_idxOf_lt hx]; omega
    have huniv : ball H {y | y ∈ σ.take (σ.idxOf x + 1)} T = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← hball x]
      exact ball_mono_set (by simpa using hmem)
    refine ⟨?_, ?_⟩
    · ext a b; simp [view, restrict, huniv]
    · simp only [view]
      rw [List.getLast?_take]
      have := List.idxOf_lt_length_of_mem hx
      simp [List.getElem?_eq_getElem this, List.getElem_idxOf]
  have hex : ∃ χ : ι → L, ∀ x y, H.Adj x y → χ x ≠ χ y := hcol
  intro x y hxy
  have hx := hview x (hσ.2 x)
  have hy := hview y (hσ.2 y)
  simp only [Algorithm.label, seeAll, hx.1, hy.1, hx.2, hy.2, dite_eq_left_of_eq_true (eq_true hex),
    Option.map_some, Option.getD_some]
  exact hex.choose_spec x y hxy

/-- **Non-vacuity** for a host graph: if radius-`T` balls of `G` are everything and `G` is
`L`-colourable, then `seeAll` solves `L`-colouring of `G` with locality `T` (for every identifier
assignment and every reveal order). -/
theorem seeAll_colors [DecidableEq ι] [Inhabited L] {G : SimpleGraph V} {T : ℕ}
    (hball : ∀ x, ball G {x} T = Set.univ) (hcol : ∃ χ : V → L, ∀ x y, G.Adj x y → χ x ≠ χ y) :
    (seeAll (ι := ι) L).Colors G T := by
  intro pos σ hσ
  refine seeAll_properOn (fun x => ?_) ?_ hσ
  · rw [ball_comap_equiv, Set.image_singleton, hball, Set.preimage_univ]
  · obtain ⟨χ, hχ⟩ := hcol
    exact ⟨χ ∘ pos, fun x y h => hχ _ _ h⟩

end NonVacuity

end Cslib.OnlineLocal
