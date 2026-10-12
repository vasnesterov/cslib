/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Foundations.Combinatorics.SimpleGraph.Girth

/-!
# Blocking sets (Bodwin–Patel, PODC'19) and dense high-girth subgraphs

A `t`-blocking set of `G` is a set `B ⊆ V × E(G)` of vertex–edge pairs `(x, e)` with `x ∉ e` such
that every cycle of length `≤ t` contains both the vertex and the edge of some pair of `B`.

* `IsBlockingSet G t B` — Definition 2 of Dinitz–Robelle (PODC'20) / Bodwin–Patel.
* `IsBlockingSet.exists_dense_subgraph` — Lemma 7 of Dinitz–Robelle with explicit constants: if
  `|B| ≤ D · |E(H)|` and `2 D s ≤ n`, some `s`-vertex set `S` carries a subgraph `H' ≤ H` of girth
  `> 2k` with `|E(H)| · s (s - 1) ≤ 2 n (n - 1) · |E(H')|` (averaging over all `s`-subsets).
* `IsBlockingSet.ncard_edgeSet_mul_le` — combined with the Moore bound: if moreover `s ≤ d ^ k`,
  then `|E(H)| · (s - 1) ≤ 2 d n (n - 1)`.
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*}

/-- `B` is a `t`-blocking set of `G` (Definition 2 of Dinitz–Robelle, after Bodwin–Patel):
every pair `(x, e) ∈ B` has `e ∈ E(G)` and `x ∉ e`, and every cycle `C` of `G` with `|C| ≤ t`
contains the vertex `x` and the edge `e` of some `(x, e) ∈ B`. -/
def IsBlockingSet (G : SimpleGraph V) (t : ℕ) (B : Finset (V × Sym2 V)) : Prop :=
  (∀ p ∈ B, p.2 ∈ G.edgeSet ∧ p.1 ∉ p.2) ∧
    ∀ v (c : G.Walk v v), c.IsCycle → c.length ≤ t → ∃ p ∈ B, p.1 ∈ c.support ∧ p.2 ∈ c.edges

/-! ### Helpers for Lemma 7: averaging over `s`-subsets -/

section Lemma7

variable [Fintype V] [DecidableEq V]

/-- The number of `s`-subsets of `V` containing a fixed set `T`, in multiplicative form:
`N_T · n^{(|T|)} = C(n, s) · s^{(|T|)}` (falling factorials), valid for all `s` and `T`. -/
lemma card_filter_powersetCard_superset_mul (T : Finset V) (s : ℕ) :
    #((univ.powersetCard s).filter (T ⊆ ·)) * (Fintype.card V).descFactorial #T =
      (Fintype.card V).choose s * s.descFactorial #T := by
  by_cases hTs : #T ≤ s
  · rw [card_filter_powersetCard_subset T univ s (subset_univ _) hTs, card_univ,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
    have := Nat.choose_mul (n := Fintype.card V) hTs
    calc _ = (#T).factorial *
          ((Fintype.card V).choose #T * (Fintype.card V - #T).choose (s - #T)) := by
          ring
      _ = _ := by rw [← this]; ring
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 (not_le.1 hTs), mul_zero]
    convert zero_mul _
    rw [card_eq_zero, filter_eq_empty_iff]
    intro S hS hTS
    have := card_le_card hTS
    rw [(mem_powersetCard.1 hS).2] at this
    omega

/-- Double counting: summing, over all `s`-subsets `S`, the number of `x ∈ X` whose vertex set
`T x` (of size `j`) lies inside `S`. -/
lemma sum_card_filter_subset_mul {β : Type*} (X : Finset β) (T : β → Finset V) (s j : ℕ)
    (hT : ∀ x ∈ X, #(T x) = j) :
    (∑ S ∈ univ.powersetCard s, #(X.filter (T · ⊆ S))) * (Fintype.card V).descFactorial j =
      #X * ((Fintype.card V).choose s * s.descFactorial j) := by
  have : ∑ S ∈ univ.powersetCard s, #(X.filter (T · ⊆ S)) =
      ∑ x ∈ X, #((univ.powersetCard s).filter (T x ⊆ ·)) := by
    simp only [card_filter]; exact sum_comm
  rw [this, sum_mul, sum_congr rfl fun x hx => (hT x hx) ▸
    card_filter_powersetCard_superset_mul (T x) s, sum_const, smul_eq_mul]

/-- The endpoints of `e : Sym2 V`, as a `Finset`. -/
def edgeVerts (e : Sym2 V) : Finset V := univ.filter (· ∈ e)

/-- The vertices involved in a vertex–edge pair `(x, e)`: `x` together with the endpoints of `e`. -/
def pairVerts (p : V × Sym2 V) : Finset V := insert p.1 (edgeVerts p.2)

lemma edgeVerts_subset_iff {e : Sym2 V} {S : Finset V} : edgeVerts e ⊆ S ↔ ∀ y ∈ e, y ∈ S := by
  simp [edgeVerts, subset_iff]

lemma pairVerts_subset_iff {p : V × Sym2 V} {S : Finset V} :
    pairVerts p ⊆ S ↔ p.1 ∈ S ∧ ∀ y ∈ p.2, y ∈ S := by
  simp [pairVerts, insert_subset_iff, edgeVerts_subset_iff]

lemma card_edgeVerts {e : Sym2 V} (he : ¬ e.IsDiag) : #(edgeVerts e) = 2 := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := by simpa using he
    have : edgeVerts s(a, b) = {a, b} := by ext; simp [edgeVerts]
    rw [this, card_pair hab]

lemma card_pairVerts {p : V × Sym2 V} (he : ¬ p.2.IsDiag) (hx : p.1 ∉ p.2) :
    #(pairVerts p) = 3 := by
  rw [pairVerts, card_insert_of_notMem (by simpa [edgeVerts] using hx), card_edgeVerts he]

/-- `H` restricted to `S`, with every edge `e` removed for which some `(x, e) ∈ B` lies inside `S`
(the graph `H''` in the proof of Lemma 7 of Dinitz–Robelle). -/
def blockedRestrict (H : SimpleGraph V) (B : Finset (V × Sym2 V)) (S : Finset V) :
    SimpleGraph V where
  Adj u v := H.Adj u v ∧ u ∈ S ∧ v ∈ S ∧ ∀ p ∈ B, pairVerts p ⊆ S → p.2 ≠ s(u, v)
  symm := ⟨fun u v => by
    rintro ⟨h, hu, hv, hp⟩
    exact ⟨h.symm, hv, hu, fun p hpB hpS => Sym2.eq_swap (a := v) ▸ hp p hpB hpS⟩⟩
  loopless := ⟨fun u h => H.loopless.irrefl u h.1⟩

lemma blockedRestrict_le (H : SimpleGraph V) (B : Finset (V × Sym2 V)) (S : Finset V) :
    blockedRestrict H B S ≤ H := fun _ _ h => h.1

lemma mem_edgeSet_blockedRestrict {H : SimpleGraph V} {B : Finset (V × Sym2 V)} {S : Finset V}
    {e : Sym2 V} :
    e ∈ (blockedRestrict H B S).edgeSet ↔
      e ∈ H.edgeSet ∧ edgeVerts e ⊆ S ∧ ∀ p ∈ B, pairVerts p ⊆ S → p.2 ≠ e := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [mem_edgeSet, blockedRestrict, edgeVerts_subset_iff, Sym2.mem_iff]
    constructor
    · rintro ⟨h, hu, hv, hp⟩
      exact ⟨h, by rintro y (rfl | rfl) <;> assumption, hp⟩
    · rintro ⟨h, hS, hp⟩
      exact ⟨h, hS u (Or.inl rfl), hS v (Or.inr rfl), hp⟩

omit [Fintype V] [DecidableEq V] in
/-- Every vertex of a walk starting in `S`, in a graph all of whose edges start in `S`, lies in
`S`. -/
lemma Walk.support_subset_of_adj {G : SimpleGraph V} {S : Finset V}
    (hS : ∀ a b, G.Adj a b → a ∈ S) :
    ∀ {u v : V} (w : G.Walk u v), u ∈ S → ∀ x ∈ w.support, x ∈ S
  | _, _, .nil, hu, x, hx => by simp_all
  | _, _, .cons h w, hu, x, hx => by
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hu
    · exact Walk.support_subset_of_adj hS w (hS _ _ h.symm) x hx

/-- The graph `blockedRestrict H B S` has no cycle of length `≤ t` when `B` is `t`-blocking. -/
lemma IsBlockingSet.noShortCycles_blockedRestrict {H : SimpleGraph V} {t : ℕ}
    {B : Finset (V × Sym2 V)} (hB : H.IsBlockingSet t B) (S : Finset V) :
    (blockedRestrict H B S).NoShortCycles t := by
  intro v c hc
  by_contra hlen
  replace hlen := not_lt.1 hlen
  have hle := blockedRestrict_le H B S
  obtain ⟨p, hpB, hp1, hp2⟩ :=
    hB.2 v (c.mapLe hle) (hc.mapLe hle) (by simpa using hlen)
  rw [Walk.support_mapLe_eq_support] at hp1
  rw [Walk.edges_mapLe_eq_edges] at hp2
  have he := mem_edgeSet_blockedRestrict.1 (c.edges_subset_edgeSet hp2)
  have hS : ∀ a b, (blockedRestrict H B S).Adj a b → a ∈ S := fun _ _ h => h.2.1
  have hv : v ∈ S := by
    cases c with
    | nil => exact (hc.ne_nil rfl).elim
    | cons h _ => exact hS _ _ h
  have hp1S : p.1 ∈ S := Walk.support_subset_of_adj hS c hv _ hp1
  have hp2S := edgeVerts_subset_iff.1 he.2.1
  exact he.2.2 p hpB (pairVerts_subset_iff.2 ⟨hp1S, hp2S⟩) rfl

/-- Deleting the blocked edges inside `S` loses at most `|B_S|` of the edges of `H` inside `S`. -/
lemma card_filter_sub_le_ncard_blockedRestrict (H : SimpleGraph V) [DecidablePred (· ∈ H.edgeSet)]
    (B : Finset (V × Sym2 V)) (S : Finset V) :
    (#((univ.filter (· ∈ H.edgeSet)).filter (edgeVerts · ⊆ S)) : ℤ) -
        #(B.filter (pairVerts · ⊆ S)) ≤ (blockedRestrict H B S).edgeSet.ncard := by
  set ES := (univ.filter (· ∈ H.edgeSet)).filter (edgeVerts · ⊆ S)
  set BS := B.filter (pairVerts · ⊆ S)
  have hsub : (↑(ES \ BS.image Prod.snd) : Set (Sym2 V)) ⊆ (blockedRestrict H B S).edgeSet := by
    intro e he
    rw [mem_coe, mem_sdiff, mem_filter, mem_filter] at he
    refine mem_edgeSet_blockedRestrict.2 ⟨he.1.1.2, he.1.2, fun p hpB hpS hpe => he.2 ?_⟩
    exact mem_image.2 ⟨p, mem_filter.2 ⟨hpB, hpS⟩, hpe⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h1
  have h2 := le_card_sdiff (BS.image Prod.snd) ES
  have h3 : #(BS.image Prod.snd) ≤ #BS := card_image_le
  omega

end Lemma7

/-- **Lemma 7 of Dinitz–Robelle / Lemma 4 of Bodwin–Patel** (explicit form, any cycle-length bound
`t`): if `B` is a `t`-blocking set with `|B| ≤ D · |E(H)|` and `2 D s ≤ n`, some `s`-set `S` carries
a subgraph `H' ≤ H` of girth `> t` with `|E(H)| · s (s - 1) ≤ 2 n (n - 1) · |E(H')|`. -/
theorem IsBlockingSet.exists_dense_subgraph_of_le [Fintype V] {H : SimpleGraph V}
    {t D s : ℕ} {B : Finset (V × Sym2 V)} (hB : H.IsBlockingSet t B)
    (hBcard : #B ≤ D * H.edgeSet.ncard) (hD : 1 ≤ D) (hs : 2 * D * s ≤ Fintype.card V) :
    ∃ S : Finset V, #S = s ∧ ∃ H' : SimpleGraph V, H' ≤ H ∧ (∀ u v, H'.Adj u v → u ∈ S) ∧
      H'.NoShortCycles t ∧
      H.edgeSet.ncard * (s * (s - 1)) ≤
        2 * (Fintype.card V * (Fintype.card V - 1)) * H'.edgeSet.ncard := by
  classical
  classical
  set n := Fintype.card V with hn
  have hsn : s ≤ n := le_trans (by nlinarith) hs
  set P := (univ : Finset V).powersetCard s with hPdef
  have hP : P.Nonempty := powersetCard_nonempty.2 (by simpa [card_univ] using hsn)
  suffices ∃ S ∈ P, H.edgeSet.ncard * (s * (s - 1)) ≤
      2 * (n * (n - 1)) * (blockedRestrict H B S).edgeSet.ncard by
    obtain ⟨S, hSP, hS⟩ := this
    exact ⟨S, (mem_powersetCard.1 hSP).2, blockedRestrict H B S, blockedRestrict_le H B S,
      fun _ _ h => h.2.1, hB.noShortCycles_blockedRestrict S, hS⟩
  rcases (show s ≤ 1 ∨ 2 ≤ s by omega) with hs1 | hs2
  · obtain ⟨S, hS⟩ := hP
    refine ⟨S, hS, ?_⟩
    have : s * (s - 1) = 0 := by rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;> rfl
    simp [this]
  have hn4 : 4 ≤ n := by nlinarith
  -- the edges of `H`, as a finset
  set E := univ.filter (· ∈ H.edgeSet) with hE
  have hm : H.edgeSet.ncard = #E := by
    rw [← Set.ncard_coe_finset]; congr 1; ext e; simp [E]
  have F1 := sum_card_filter_subset_mul E edgeVerts s 2 fun e he =>
    card_edgeVerts (H.not_isDiag_of_mem_edgeSet (mem_filter.1 he).2)
  have F2 := sum_card_filter_subset_mul B pairVerts s 3 fun p hp =>
    card_pairVerts (H.not_isDiag_of_mem_edgeSet (hB.1 p hp).1) (hB.1 p hp).2
  have F3 : (∑ S ∈ P, (#(E.filter (edgeVerts · ⊆ S)) : ℤ)) -
      ∑ S ∈ P, (#(B.filter (pairVerts · ⊆ S)) : ℤ) ≤
        ∑ S ∈ P, ((blockedRestrict H B S).edgeSet.ncard : ℤ) := by
    rw [← sum_sub_distrib]
    exact sum_le_sum fun S _ => card_filter_sub_le_ncard_blockedRestrict H B S
  apply exists_le_of_sum_le hP
  rw [sum_const, smul_eq_mul, card_powersetCard, card_univ, ← mul_sum, hm]
  rw [hm] at hBcard
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, ← hn, ← hPdef, Nat.sub_zero,
    mul_one] at F1 F2
  simp only [← Nat.cast_sum] at F3
  generalize ∑ S ∈ P, #(E.filter (edgeVerts · ⊆ S)) = A at F1 F3
  generalize ∑ S ∈ P, #(B.filter (pairVerts · ⊆ S)) = A' at F2 F3
  generalize ∑ S ∈ P, (blockedRestrict H B S).edgeSet.ncard = G at F3 ⊢
  generalize n.choose s = c at F1 F2 ⊢
  generalize #E = m at *
  generalize #B = b at *
  zify [show 1 ≤ n by omega, show 2 ≤ n by omega, show 1 ≤ s by omega, hs2] at F1 F2 hs hBcard ⊢
  -- pure arithmetic in `ℤ`
  have hn4' : (4 : ℤ) ≤ n := by exact_mod_cast hn4
  have hs2' : (2 : ℤ) ≤ s := by exact_mod_cast hs2
  have hD' : (1 : ℤ) ≤ D := by exact_mod_cast hD
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have hX : (0 : ℤ) ≤ c * (s * (s - 1)) := mul_nonneg (by positivity) (by nlinarith)
  have hb : 2 * (b : ℤ) * (s - 2) ≤ (n - 2) * m := by
    have h1 := mul_le_mul_of_nonneg_right hBcard (by linarith : (0 : ℤ) ≤ s - 2)
    have h2 := mul_le_mul_of_nonneg_left hs hm0
    have h3 := mul_le_mul_of_nonneg_left hD' hm0
    nlinarith
  have hG := mul_le_mul_of_nonneg_left F3
    (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (mul_nonneg (by linarith) (by linarith)) :
      (0 : ℤ) ≤ 2 * (n - 2) * ((n - 1) * n))
  have hbX := mul_le_mul_of_nonneg_right hb hX
  have key : ((n : ℤ) - 2) * (c * (m * (s * (s - 1)))) ≤ (n - 2) * (2 * (n * (n - 1)) * G) := by
    linear_combination hG + hbX - 2 * (n - 2) * F1 + 2 * F2
  exact le_of_mul_le_mul_left key (by linarith)

/-- **Lemma 7 of Dinitz–Robelle** (explicit form). -/
theorem IsBlockingSet.exists_dense_subgraph [Fintype V] {H : SimpleGraph V}
    {k D s : ℕ} {B : Finset (V × Sym2 V)} (hB : H.IsBlockingSet (2 * k) B)
    (hBcard : #B ≤ D * H.edgeSet.ncard) (hD : 1 ≤ D) (hs : 2 * D * s ≤ Fintype.card V) :
    ∃ S : Finset V, #S = s ∧ ∃ H' : SimpleGraph V, H' ≤ H ∧ (∀ u v, H'.Adj u v → u ∈ S) ∧
      H'.NoShortCycles (2 * k) ∧
      H.edgeSet.ncard * (s * (s - 1)) ≤
        2 * (Fintype.card V * (Fintype.card V - 1)) * H'.edgeSet.ncard :=
  hB.exists_dense_subgraph_of_le hBcard hD hs

/-- Lemma 7 + Moore bound: the edge bound used in Theorem 8 of Dinitz–Robelle. -/
theorem IsBlockingSet.ncard_edgeSet_mul_le [Fintype V] {H : SimpleGraph V}
    {k D s d : ℕ} {B : Finset (V × Sym2 V)} (hk : 1 ≤ k) (hB : H.IsBlockingSet (2 * k) B)
    (hBcard : #B ≤ D * H.edgeSet.ncard) (hD : 1 ≤ D) (hs : 2 * D * s ≤ Fintype.card V)
    (hsd : s ≤ d ^ k) :
    H.edgeSet.ncard * (s - 1) ≤ 2 * d * (Fintype.card V * (Fintype.card V - 1)) := by
  classical
  obtain ⟨S, hS, H', -, hH'S, hgirth, hineq⟩ := hB.exists_dense_subgraph hBcard hD hs
  have hM := hgirth.ncard_edgeSet_le hk S hH'S (hS ▸ hsd)
  rw [hS] at hM
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · simp
  refine Nat.le_of_mul_le_mul_right ?_ hs0
  calc H.edgeSet.ncard * (s - 1) * s = H.edgeSet.ncard * (s * (s - 1)) := by ring
    _ ≤ 2 * (Fintype.card V * (Fintype.card V - 1)) * H'.edgeSet.ncard := hineq
    _ ≤ 2 * (Fintype.card V * (Fintype.card V - 1)) * (d * s) := Nat.mul_le_mul_left _ hM
    _ = 2 * d * (Fintype.card V * (Fintype.card V - 1)) * s := by ring

end SimpleGraph
