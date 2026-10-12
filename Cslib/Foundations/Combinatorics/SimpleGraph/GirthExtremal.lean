/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Foundations.Combinatorics.SimpleGraph.BlockingSet

/-!
# The girth extremal function `b(N, g)`

`girthExtremal N g` is the maximum number of edges of a graph on `N` vertices with girth `> g`
(i.e. no cycle of length `≤ g`). Bodwin–Patel (PODC'19) state their size bound for fault-tolerant
greedy spanners in terms of this function.

* `NoShortCycles.ncard_le_girthExtremal` — graphs on `Fin N`;
  `NoShortCycles.ncard_le_girthExtremal_of_subset` — any graph whose edges lie inside an `N`-set.
* `girthExtremal_le_of_le_pow`, `girthExtremal_le_rpow` — Moore bounds for `b(N, 2k)`.
* `IsBlockingSet.ncard_mul_le_girthExtremal` — Lemma 4 of Bodwin–Patel in extremal form:
  `|E(H)| · s (s - 1) ≤ 2 n (n - 1) · b(s, t)` whenever `H` has a `t`-blocking set of size
  `≤ D |E(H)|` and `2 D s ≤ n`.
* `IsBlockingSet.ncard_le_girthExtremal` — explicit form:
  `|E(H)| ≤ 32 D² · max(b(⌊n / 2D⌋, t), 1)`.
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*}

/-- `b(N, g)`: the maximum number of edges of a graph on `N` vertices with no cycle of length
`≤ g` (girth `> g`). -/
noncomputable def girthExtremal (N g : ℕ) : ℕ :=
  sSup {m | ∃ G : SimpleGraph (Fin N), G.NoShortCycles g ∧ G.edgeSet.ncard = m}

/-- Short cycles pull back along graph embeddings. -/
lemma NoShortCycles.of_embedding {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {g : ℕ}
    (φ : G ↪g H) (h : H.NoShortCycles g) : G.NoShortCycles g := by
  intro v c hc
  simpa using h _ (c.map φ.toHom) (hc.map φ.injective)

private lemma girthExtremal_bddAbove (N g : ℕ) :
    BddAbove {m | ∃ G : SimpleGraph (Fin N), G.NoShortCycles g ∧ G.edgeSet.ncard = m} := by
  refine ⟨Nat.card (Sym2 (Fin N)), ?_⟩
  rintro m ⟨G, -, rfl⟩
  rw [← Set.ncard_univ]
  exact Set.ncard_le_ncard (Set.subset_univ _)

lemma NoShortCycles.ncard_le_girthExtremal {N g : ℕ} {G : SimpleGraph (Fin N)}
    (h : G.NoShortCycles g) : G.edgeSet.ncard ≤ girthExtremal N g :=
  le_csSup (girthExtremal_bddAbove N g) ⟨G, h, rfl⟩

/-- The maximum is attained. -/
lemma exists_eq_girthExtremal (N g : ℕ) :
    ∃ G : SimpleGraph (Fin N), G.NoShortCycles g ∧ G.edgeSet.ncard = girthExtremal N g :=
  Nat.sSup_mem (s := {m | ∃ G : SimpleGraph (Fin N), G.NoShortCycles g ∧ G.edgeSet.ncard = m})
    ⟨0, ⊥, fun v c hc => (hc.ne_bot rfl).elim, by simp⟩ (girthExtremal_bddAbove N g)

/-- A graph of girth `> g` whose edges lie inside a set `S` has at most `b(|S|, g)` edges. -/
theorem NoShortCycles.ncard_le_girthExtremal_of_subset {G : SimpleGraph V} {g : ℕ}
    (h : G.NoShortCycles g) (S : Finset V) (hS : ∀ u v, G.Adj u v → u ∈ S) :
    G.edgeSet.ncard ≤ girthExtremal #S g := by
  let f : Fin #S ↪ V := S.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have hf : ∀ x : S, f (S.equivFin x) = x := fun x => by simp [f]
  let G' : SimpleGraph (Fin #S) := G.comap f
  have h' : G'.NoShortCycles g := h.of_embedding (Embedding.comap f G)
  refine le_trans ?_ h'.ncard_le_girthExtremal
  have hsub : G.edgeSet ⊆ Sym2.map f '' G'.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hu := hS u v he
      have hv := hS v u (G.adj_symm he)
      refine ⟨s(S.equivFin ⟨u, hu⟩, S.equivFin ⟨v, hv⟩), ?_, ?_⟩
      · simp only [mem_edgeSet, G', comap_adj]
        rw [hf, hf]; exact he
      · change s(f _, f _) = _
        rw [hf, hf]
  calc G.edgeSet.ncard ≤ (Sym2.map f '' G'.edgeSet).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = G'.edgeSet.ncard := Set.ncard_image_of_injective _ (Sym2.map.injective f.injective)

/-- **Moore bound** for the extremal function: `b(N, 2k) ≤ d N` whenever `N ≤ d ^ k`. -/
theorem girthExtremal_le_of_le_pow {N k d : ℕ} (hk : 1 ≤ k) (hN : N ≤ d ^ k) :
    girthExtremal N (2 * k) ≤ d * N := by
  obtain ⟨G, hG, hE⟩ := exists_eq_girthExtremal N (2 * k)
  rw [← hE]
  simpa using hG.ncard_edgeSet_le hk univ (by simp) (by simpa using hN)

/-- **Moore bound**: `b(N, 2k) ≤ N^{1+1/k} + N`. -/
theorem girthExtremal_le_rpow {N k : ℕ} (hk : 1 ≤ k) :
    (girthExtremal N (2 * k) : ℝ) ≤ (N : ℝ) ^ (1 + 1 / (k : ℝ)) + N := by
  obtain ⟨G, hG, hE⟩ := exists_eq_girthExtremal N (2 * k)
  rw [← hE]
  simpa using hG.ncard_edgeSet_le_rpow hk

/-- **Lemma 4 of Bodwin–Patel** (extremal form). -/
theorem IsBlockingSet.ncard_mul_le_girthExtremal [Fintype V] {H : SimpleGraph V}
    {t D s : ℕ} {B : Finset (V × Sym2 V)} (hB : H.IsBlockingSet t B)
    (hBcard : #B ≤ D * H.edgeSet.ncard) (hD : 1 ≤ D) (hs : 2 * D * s ≤ Fintype.card V) :
    H.edgeSet.ncard * (s * (s - 1)) ≤
      2 * (Fintype.card V * (Fintype.card V - 1)) * girthExtremal s t := by
  classical
  obtain ⟨S, hS, H', -, hH'S, hgirth, hineq⟩ := hB.exists_dense_subgraph_of_le hBcard hD hs
  have := hgirth.ncard_le_girthExtremal_of_subset S hH'S
  rw [hS] at this
  exact hineq.trans (Nat.mul_le_mul_left _ this)

private lemma two_mul_ncard_edgeSet_le [Fintype V] (G : SimpleGraph V) :
    2 * G.edgeSet.ncard ≤ Fintype.card V * (Fintype.card V - 1) := by
  classical
  have h := G.card_edgeFinset_le_card_choose_two
  rw [Nat.choose_two_right] at h
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  have := Nat.mul_div_le (Fintype.card V * (Fintype.card V - 1)) 2
  omega

/-- **Theorem 1 of Bodwin–Patel, abstract form**: a graph on `n` vertices with a `t`-blocking set of
size `≤ D · |E(H)|` (`D ≥ 1`) has at most `32 D² · max(b(⌊n / 2D⌋, t), 1)` edges. -/
theorem IsBlockingSet.ncard_le_girthExtremal [Fintype V] {H : SimpleGraph V}
    {t D : ℕ} {B : Finset (V × Sym2 V)} (hB : H.IsBlockingSet t B)
    (hBcard : #B ≤ D * H.edgeSet.ncard) (hD : 1 ≤ D) :
    H.edgeSet.ncard ≤ 32 * D ^ 2 * max (girthExtremal (Fintype.card V / (2 * D)) t) 1 := by
  classical
  set n := Fintype.card V with hn
  set s := n / (2 * D) with hsdef
  set b := girthExtremal s t
  set m := H.edgeSet.ncard with hm
  have hm2 : 2 * m ≤ n * (n - 1) := two_mul_ncard_edgeSet_le H
  have hnn : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hb1 : 1 ≤ max b 1 := le_max_right _ _
  have hbb : b ≤ max b 1 := le_max_left _ _
  rcases lt_or_ge n (8 * D) with hlt | hge
  · have h64 : n * n < 64 * D ^ 2 := by nlinarith
    have : m < 32 * D ^ 2 := by omega
    calc m ≤ 32 * D ^ 2 := this.le
      _ = 32 * D ^ 2 * 1 := (mul_one _).symm
      _ ≤ 32 * D ^ 2 * max b 1 := Nat.mul_le_mul_left _ hb1
  · have h2D : 0 < 2 * D := by omega
    have hs4 : 4 ≤ s := (Nat.le_div_iff_mul_le h2D).2 (by omega)
    have hsn : 2 * D * s ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n (2 * D)
    have hlt : n < s * (2 * D) + 2 * D := Nat.lt_div_mul_add h2D
    have key : m * (s * (s - 1)) ≤ 2 * (n * (n - 1)) * b :=
      hB.ncard_mul_le_girthExtremal hBcard hD hsn
    clear_value b m s n
    obtain ⟨r, rfl⟩ : ∃ r, s = r + 3 := ⟨s - 3, by omega⟩
    have hn1 : n ≤ 4 * D * (r + 2) := by nlinarith
    have hn2 : n ≤ 4 * D * (r + 3) := by nlinarith
    have hsq : n * n ≤ 16 * D ^ 2 * ((r + 3) * (r + 2)) := by
      calc n * n ≤ (4 * D * (r + 3)) * (4 * D * (r + 2)) := Nat.mul_le_mul hn2 hn1
        _ = 16 * D ^ 2 * ((r + 3) * (r + 2)) := by ring
    have hr : (r + 3) - 1 = r + 2 := by omega
    rw [hr] at key
    have hnpos : 0 < n * n := Nat.mul_pos (by omega) (by omega)
    have : m * (n * n) ≤ 32 * D ^ 2 * b * (n * n) := by
      calc m * (n * n) ≤ m * (16 * D ^ 2 * ((r + 3) * (r + 2))) := Nat.mul_le_mul_left _ hsq
        _ = 16 * D ^ 2 * (m * ((r + 3) * (r + 2))) := by ring
        _ ≤ 16 * D ^ 2 * (2 * (n * (n - 1)) * b) := Nat.mul_le_mul_left _ key
        _ ≤ 16 * D ^ 2 * (2 * (n * n) * b) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hnn))
        _ = 32 * D ^ 2 * b * (n * n) := by ring
    calc m ≤ 32 * D ^ 2 * b := Nat.le_of_mul_le_mul_right this hnpos
      _ ≤ 32 * D ^ 2 * max b 1 := Nat.mul_le_mul_left _ hbb

end SimpleGraph
