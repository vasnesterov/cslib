/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Algebra.Order.Sub.Basic

/-!
# Dynamic networks: products of communication graphs

A *dynamic network* on a vertex type `α` is a sequence `G : ℕ → α → α → Prop` of directed
communication graphs, `G t x y` meaning that `x` successfully sends to `y` in round `t`.
Information propagates along *products* (relational compositions) of consecutive rounds:
`y` has heard of `x` after rounds `a, …, a + k - 1` iff `prod G a k x y`.

This is the "heard-of" / oblivious message adversary setting (Charron-Bost–Schiper; Zeiner,
Schwarz, Schmid; El-Hayek, Henzinger, Schmid).

## Main definitions

* `DynNet.prod G a k`: the product graph `G a ∘ G (a+1) ∘ ⋯ ∘ G (a+k-1)` (`(· = ·)` for `k = 0`).
* `DynNet.inNbhd G t t' x`, `DynNet.outNbhd G t t' x`: in- and out-neighbourhood of `x` in the
  product of rounds `t, …, t'` (`{x}` if `t = t' + 1`, `∅` if `t > t' + 1`).
* `DynNet.Broadcasts G t`: after rounds `1, …, t` some process has reached every process.
* `DynNet.broadcastTime G`, `DynNet.advBroadcastTime 𝒢`: broadcast time of a sequence and of an
  oblivious message adversary (a set of allowed graphs).
* `DynNet.IsRoot E r`: every vertex is reachable from `r` in `E`.

## Main results

* `prod_add`, `prod_succ'`: associativity of products.
* `prod_mono`: with self-loops, products only grow when the interval of rounds grows.
* `prod_of_inv`: a property preserved by every edge of every round holds along products (forward
  invariants, "speed of information" arguments).
* `mem_outNbhd_iff_mem_inNbhd`, `outNbhd_trans`, `inNbhd_mono`, `outNbhd_mono`: basic properties of
  generalized neighbourhoods.
* `card_inNbhd_lt_of_root_notMem`, `card_outNbhd_lt_of_root_mem`: in a rooted round the
  neighbourhoods strictly grow.
-/

@[expose] public section

namespace Cslib.DynNet

open Finset Relation

variable {α : Type*}

/-- The product graph of `k` consecutive rounds starting at round `a`:
`prod G a k = G a ∘ G (a+1) ∘ ⋯ ∘ G (a+k-1)`, where `(A ∘ B) x y ↔ ∃ z, A x z ∧ B z y`;
the empty product is the identity relation. -/
def prod (G : ℕ → α → α → Prop) (a : ℕ) : ℕ → α → α → Prop
  | 0 => (· = ·)
  | k + 1 => Relation.Comp (prod G a k) (G (a + k))

variable {G : ℕ → α → α → Prop}

@[simp] theorem prod_zero (a : ℕ) : prod G a 0 = (· = ·) := rfl

theorem prod_succ (a k : ℕ) : prod G a (k + 1) = Relation.Comp (prod G a k) (G (a + k)) := rfl

@[simp] theorem prod_one (a : ℕ) : prod G a 1 = G a := by
  rw [prod_succ, prod_zero, Nat.add_zero, Relation.eq_comp]

theorem prod_add (a k l : ℕ) :
    prod G a (k + l) = Relation.Comp (prod G a k) (prod G (a + k) l) := by
  induction l with
  | zero => simp [Relation.comp_eq]
  | succ l ih =>
    rw [← Nat.add_assoc, prod_succ, ih, prod_succ, Relation.comp_assoc, Nat.add_assoc]

theorem prod_succ' (a k : ℕ) : prod G a (k + 1) = Relation.Comp (G a) (prod G (a + 1) k) := by
  rw [Nat.add_comm, prod_add, prod_one]

theorem prod_succ_apply {a k : ℕ} {x y : α} :
    prod G a (k + 1) x y ↔ ∃ z, prod G a k x z ∧ G (a + k) z y := by
  rw [prod_succ]; rfl

theorem prod_succ'_apply {a k : ℕ} {x y : α} :
    prod G a (k + 1) x y ↔ ∃ z, G a x z ∧ prod G (a + 1) k z y := by
  rw [prod_succ']; rfl

theorem prod_add_apply {a k l : ℕ} {x y : α} :
    prod G a (k + l) x y ↔ ∃ z, prod G a k x z ∧ prod G (a + k) l z y := by
  rw [prod_add]; rfl

theorem prod_trans {a k l : ℕ} {x y z : α} (h₁ : prod G a k x y) (h₂ : prod G (a + k) l y z) :
    prod G a (k + l) x z :=
  prod_add_apply.2 ⟨y, h₁, h₂⟩

/-- With a self-loop at every node in every round, every product is reflexive. -/
theorem prod_refl (hG : ∀ i x, G i x x) (a k : ℕ) (x : α) : prod G a k x x := by
  induction k with
  | zero => rfl
  | succ k ih => exact prod_succ_apply.2 ⟨x, ih, hG _ x⟩

/-- **Monotonicity of products.** With self-loops, if the rounds `[a, a + k)` are contained in
`[a', a' + k')`, then the product over the former is contained in the product over the latter. -/
theorem prod_mono (hG : ∀ i x, G i x x) {a k a' k' : ℕ} (h₁ : a' ≤ a)
    (h₂ : a + k ≤ a' + k') {x y : α} (h : prod G a k x y) : prod G a' k' x y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h₁
  obtain ⟨e, he⟩ : ∃ e, k' = d + k + e := ⟨k' - (d + k), by omega⟩
  subst he
  have h1 : prod G a' (d + k) x y := prod_trans (prod_refl hG _ _ x) h
  exact prod_trans h1 (prod_refl hG _ _ y)

/-- **Forward invariant along a product of rounds.** If `S 0 x` holds and every edge of round
`a + k` maps `S k` into `S (k + 1)`, then every vertex reached from `x` by the product of the `k`
rounds starting at round `a` satisfies `S k`. -/
theorem prod_of_inv {E : ℕ → α → α → Prop} (S : ℕ → α → Prop) {a : ℕ} {x : α} (h0 : S 0 x)
    (hstep : ∀ k z y, S k z → E (a + k) z y → S (k + 1) y) :
    ∀ k y, prod E a k x y → S k y := by
  intro k
  induction k with
  | zero => rintro y rfl; exact h0
  | succ k ih =>
    intro y hy
    obtain ⟨z, hz, hzy⟩ := prod_succ_apply.1 hy
    exact hstep k z y (ih z hz) hzy

/-! ### Generalized neighbourhoods -/

section Nbhd

variable [Fintype α]

open Classical in
/-- The in-neighbourhood `I_t^{t'}(x)` of `x` between rounds `t` and `t'`: the in-neighbourhood of
`x` in `G t ∘ ⋯ ∘ G t'` if `t ≤ t'`, `{x}` if `t = t' + 1`, and `∅` otherwise
(Definition 2.1 of El-Hayek–Henzinger–Schmid). -/
noncomputable def inNbhd (G : ℕ → α → α → Prop) (t t' : ℕ) (x : α) : Finset α :=
  if t ≤ t' + 1 then univ.filter (fun y => prod G t (t' + 1 - t) y x) else ∅

open Classical in
/-- The out-neighbourhood `O_t^{t'}(x)` of `x` between rounds `t` and `t'`
(Definition 2.2 of El-Hayek–Henzinger–Schmid). -/
noncomputable def outNbhd (G : ℕ → α → α → Prop) (t t' : ℕ) (x : α) : Finset α :=
  if t ≤ t' + 1 then univ.filter (fun y => prod G t (t' + 1 - t) x y) else ∅

theorem mem_inNbhd {t t' : ℕ} {x y : α} :
    y ∈ inNbhd G t t' x ↔ t ≤ t' + 1 ∧ prod G t (t' + 1 - t) y x := by
  unfold inNbhd; split_ifs with h <;> simp [h]

theorem mem_outNbhd {t t' : ℕ} {x y : α} :
    y ∈ outNbhd G t t' x ↔ t ≤ t' + 1 ∧ prod G t (t' + 1 - t) x y := by
  unfold outNbhd; split_ifs with h <;> simp [h]

theorem inNbhd_succ_self (t : ℕ) (x : α) : inNbhd G (t + 1) t x = {x} := by
  ext y; simp [mem_inNbhd]

theorem outNbhd_succ_self (t : ℕ) (x : α) : outNbhd G (t + 1) t x = {x} := by
  ext y; simp [mem_outNbhd, eq_comm]

theorem inNbhd_of_lt {t t' : ℕ} (h : t' + 1 < t) (x : α) : inNbhd G t t' x = ∅ := by
  ext y; simp [mem_inNbhd]; omega

theorem outNbhd_of_lt {t t' : ℕ} (h : t' + 1 < t) (x : α) : outNbhd G t t' x = ∅ := by
  ext y; simp [mem_outNbhd]; omega

/-- For `t ≤ t'`, `I_t^{t'}(x)` is the in-neighbourhood in the product of rounds `t, …, t'`. -/
theorem mem_inNbhd_of_le {t t' : ℕ} (h : t ≤ t') {x y : α} :
    y ∈ inNbhd G t t' x ↔ prod G t (t' + 1 - t) y x := by
  rw [mem_inNbhd]; simp only [and_iff_right_iff_imp]; intro; omega

theorem mem_outNbhd_of_le {t t' : ℕ} (h : t ≤ t') {x y : α} :
    y ∈ outNbhd G t t' x ↔ prod G t (t' + 1 - t) x y := by
  rw [mem_outNbhd]; simp only [and_iff_right_iff_imp]; intro; omega

/-- Lemma 2.3: `x ∈ O_t^{t'}(y) ↔ y ∈ I_t^{t'}(x)`. -/
theorem mem_outNbhd_iff_mem_inNbhd {t t' : ℕ} {x y : α} :
    x ∈ outNbhd G t t' y ↔ y ∈ inNbhd G t t' x := by
  rw [mem_outNbhd, mem_inNbhd]

/-- Lemma 2.4 (i) (transitivity): if `y ∈ O_t^{t'}(x)` and `z ∈ O_{t'+1}^{t''}(y)`, then
`z ∈ O_t^{t''}(x)`. -/
theorem outNbhd_trans {t t' t'' : ℕ} {x y z : α} (h₁ : y ∈ outNbhd G t t' x)
    (h₂ : z ∈ outNbhd G (t' + 1) t'' y) : z ∈ outNbhd G t t'' x := by
  rw [mem_outNbhd] at h₁ h₂ ⊢
  obtain ⟨h₁, p₁⟩ := h₁
  obtain ⟨h₂, p₂⟩ := h₂
  refine ⟨by omega, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, t' + 1 = t + k := ⟨t' + 1 - t, by omega⟩
  obtain ⟨l, hl⟩ : ∃ l, t'' + 1 = t' + 1 + l := ⟨t'' + 1 - (t' + 1), by omega⟩
  rw [hk, Nat.add_sub_cancel_left] at p₁
  rw [hl, Nat.add_sub_cancel_left, hk] at p₂
  rw [hl, hk, Nat.add_assoc, Nat.add_sub_cancel_left]
  exact prod_trans p₁ p₂

/-- Lemma 2.4 (ii). -/
theorem outNbhd_trans_of_mem_inNbhd {t t' t'' : ℕ} {x y z : α} (h₁ : x ∈ inNbhd G t t' y)
    (h₂ : z ∈ outNbhd G (t' + 1) t'' y) : z ∈ outNbhd G t t'' x :=
  outNbhd_trans (mem_outNbhd_iff_mem_inNbhd.2 h₁) h₂

/-- Lemma 2.4 (iii). -/
theorem outNbhd_trans_of_mem_inNbhd_of_mem_inNbhd {t t' t'' : ℕ} {x y z : α}
    (h₁ : x ∈ inNbhd G t t' y) (h₂ : y ∈ inNbhd G (t' + 1) t'' z) : z ∈ outNbhd G t t'' x :=
  outNbhd_trans (mem_outNbhd_iff_mem_inNbhd.2 h₁) (mem_outNbhd_iff_mem_inNbhd.2 h₂)

/-- Transitivity, in-neighbourhood form: if `y ∈ I_{t'+1}^{t''}(z)` and `x ∈ I_t^{t'}(y)` then
`x ∈ I_t^{t''}(z)`. -/
theorem inNbhd_trans {t t' t'' : ℕ} {x y z : α} (h₁ : x ∈ inNbhd G t t' y)
    (h₂ : y ∈ inNbhd G (t' + 1) t'' z) : x ∈ inNbhd G t t'' z :=
  mem_outNbhd_iff_mem_inNbhd.1 (outNbhd_trans_of_mem_inNbhd_of_mem_inNbhd h₁ h₂)

/-- Lemma 2.5 (i) (monotonicity): with self-loops, `I_{t₂}^{t₃}(x) ⊆ I_{t₁}^{t₄}(x)` for `t₁ ≤ t₂`,
`t₃ ≤ t₄`. -/
theorem inNbhd_mono (hG : ∀ i x, G i x x) {t₁ t₂ t₃ t₄ : ℕ} (h₁₂ : t₁ ≤ t₂) (h₃₄ : t₃ ≤ t₄)
    (x : α) : inNbhd G t₂ t₃ x ⊆ inNbhd G t₁ t₄ x := by
  intro y hy
  rw [mem_inNbhd] at hy ⊢
  exact ⟨by omega, prod_mono hG h₁₂ (by omega) hy.2⟩

/-- Lemma 2.5 (ii) (monotonicity): with self-loops, `O_{t₂}^{t₃}(x) ⊆ O_{t₁}^{t₄}(x)`. -/
theorem outNbhd_mono (hG : ∀ i x, G i x x) {t₁ t₂ t₃ t₄ : ℕ} (h₁₂ : t₁ ≤ t₂) (h₃₄ : t₃ ≤ t₄)
    (x : α) : outNbhd G t₂ t₃ x ⊆ outNbhd G t₁ t₄ x := by
  intro y hy
  rw [mem_outNbhd] at hy ⊢
  exact ⟨by omega, prod_mono hG h₁₂ (by omega) hy.2⟩

theorem self_mem_inNbhd (hG : ∀ i x, G i x x) {t t' : ℕ} (h : t ≤ t' + 1) (x : α) :
    x ∈ inNbhd G t t' x :=
  mem_inNbhd.2 ⟨h, prod_refl hG _ _ x⟩

theorem self_mem_outNbhd (hG : ∀ i x, G i x x) {t t' : ℕ} (h : t ≤ t' + 1) (x : α) :
    x ∈ outNbhd G t t' x :=
  mem_outNbhd.2 ⟨h, prod_refl hG _ _ x⟩

end Nbhd

/-! ### Rooted rounds -/

/-- `r` is a root of the graph `E`: every vertex is reachable from `r` along `E`-edges. -/
def IsRoot (E : α → α → Prop) (r : α) : Prop := ∀ y, ReflTransGen E r y

/-- A path from outside a set into it crosses the boundary: if `ReflTransGen E a b`, `a ∉ S` and
`b ∈ S`, then some edge `E z y` has `z ∉ S`, `y ∈ S`. -/
theorem exists_edge_cross {E : α → α → Prop} {S : α → Prop} {a b : α} (h : ReflTransGen E a b)
    (ha : ¬ S a) (hb : S b) : ∃ z y, E z y ∧ ¬ S z ∧ S y := by
  induction h with
  | refl => exact absurd hb ha
  | tail _ hcd ih =>
    rename_i c d _
    by_cases hc : S c
    · exact ih hc
    · exact ⟨c, d, hcd, hc, hb⟩

section Rooted

variable [Fintype α]

/-- Lemma 3.2 (i) of El-Hayek–Henzinger–Schmid: if the root `r` of round `t` is not in
`I_{t+1}^{t'}(x)`, then `|I_t^{t'}(x)| > |I_{t+1}^{t'}(x)|`. -/
theorem card_inNbhd_lt_of_root_notMem (hG : ∀ i x, G i x x) {t t' : ℕ} (htt' : t ≤ t')
    {r : α} (hr : IsRoot (G t) r) {x : α} (hx : r ∉ inNbhd G (t + 1) t' x) :
    (inNbhd G (t + 1) t' x).card < (inNbhd G t t' x).card := by
  have hsub : inNbhd G (t + 1) t' x ⊆ inNbhd G t t' x := inNbhd_mono hG (Nat.le_succ t) le_rfl x
  obtain ⟨z, y, hzy, hz, hy⟩ := exists_edge_cross (S := (· ∈ inNbhd G (t + 1) t' x)) (hr x) hx
    (self_mem_inNbhd hG (by omega) x)
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset hsub |>.2 ⟨z, ?_, hz⟩
  have hz' : z ∈ inNbhd G t t y := by
    rw [mem_inNbhd_of_le le_rfl, Nat.add_sub_cancel_left, prod_one]; exact hzy
  exact inNbhd_trans hz' hy

/-- Lemma 3.2 (ii) of El-Hayek–Henzinger–Schmid: if the root `r` of round `t'+1` is in
`O_t^{t'}(x)` and `|O_t^{t'}(x)| < n`, then `|O_t^{t'+1}(x)| > |O_t^{t'}(x)|`. -/
theorem card_outNbhd_lt_of_root_mem (hG : ∀ i x, G i x x) {t t' : ℕ}
    {r : α} (hr : IsRoot (G (t' + 1)) r) {x : α} (hx : r ∈ outNbhd G t t' x)
    (hn : (outNbhd G t t' x).card < Fintype.card α) :
    (outNbhd G t t' x).card < (outNbhd G t (t' + 1) x).card := by
  have hsub : outNbhd G t t' x ⊆ outNbhd G t (t' + 1) x := outNbhd_mono hG le_rfl (Nat.le_succ t') x
  obtain ⟨b, hb⟩ : ∃ b, b ∉ outNbhd G t t' x := by
    by_contra! h
    exact (Finset.eq_univ_iff_forall.2 h ▸ hn).ne Finset.card_univ
  obtain ⟨y, z, hyz, hy, hz⟩ :=
    exists_edge_cross (S := (· ∉ outNbhd G t t' x)) (hr b) (not_not.2 hx) hb
  rw [not_not] at hy
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset hsub |>.2 ⟨z, ?_, hz⟩
  have hz' : z ∈ outNbhd G (t' + 1) (t' + 1) y := by
    rw [mem_outNbhd_of_le le_rfl, Nat.add_sub_cancel_left, prod_one]; exact hyz
  exact outNbhd_trans hy hz'

end Rooted

/-! ### Broadcast -/

/-- After rounds `1, …, t`, some process `x` has reached every process:
`∃ x, ∀ y, (x, y) ∈ G 1 ∘ ⋯ ∘ G t`. -/
def Broadcasts (G : ℕ → α → α → Prop) (t : ℕ) : Prop := ∃ x, ∀ y, prod G 1 t x y

/-- The broadcast time `t*(G₁, G₂, …) = min {t ∈ ℕ : ∃ x, ∀ y, (x, y) ∈ G₁ ∘ ⋯ ∘ Gₜ}`
(Definition 2.2 of the brief announcement / 1.3 of the full version). Junk value `0` if broadcast
never happens. -/
noncomputable def broadcastTime (G : ℕ → α → α → Prop) : ℕ := sInf {t | Broadcasts G t}

/-- The broadcast time of an (oblivious message) adversary `𝒢`: the supremum of the broadcast times
of all sequences of graphs from `𝒢` (Definition 2.3 of the brief announcement). Junk value `0` if
unbounded. -/
noncomputable def advBroadcastTime (𝒢 : Set (α → α → Prop)) : ℕ :=
  ⨆ G : {G : ℕ → α → α → Prop // ∀ i, G i ∈ 𝒢}, broadcastTime G.1

/-- With self-loops, once a process has broadcast it stays broadcast. -/
theorem Broadcasts.mono (hG : ∀ i x, G i x x) {t t' : ℕ} (h : Broadcasts G t)
    (htt' : t ≤ t') : Broadcasts G t' := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, fun y => prod_mono hG le_rfl (by omega) (hx y)⟩

theorem broadcastTime_le {t : ℕ} (h : Broadcasts G t) : broadcastTime G ≤ t :=
  Nat.sInf_le h

theorem le_broadcastTime {t : ℕ} (hex : ∃ s, Broadcasts G s) (h : ∀ s < t, ¬ Broadcasts G s) :
    t ≤ broadcastTime G := by
  by_contra! hlt
  exact h _ hlt (Nat.sInf_mem hex)

/-- If every sequence over `𝒢` broadcasts by round `T`, then `t*(𝒢) ≤ T`. -/
theorem advBroadcastTime_le {𝒢 : Set (α → α → Prop)} {T : ℕ}
    (h : ∀ G : ℕ → α → α → Prop, (∀ i, G i ∈ 𝒢) → Broadcasts G T) : advBroadcastTime 𝒢 ≤ T := by
  unfold advBroadcastTime
  rcases isEmpty_or_nonempty {G : ℕ → α → α → Prop // ∀ i, G i ∈ 𝒢} with hE | hE
  · simp
  · exact ciSup_le fun G => broadcastTime_le (h G.1 G.2)

/-- A sequence over `𝒢` that does not broadcast before round `t` shows `t ≤ t*(𝒢)`, provided all
sequences over `𝒢` broadcast by some fixed round `T`. -/
theorem le_advBroadcastTime {𝒢 : Set (α → α → Prop)} {T : ℕ}
    (hT : ∀ G : ℕ → α → α → Prop, (∀ i, G i ∈ 𝒢) → Broadcasts G T)
    {G : ℕ → α → α → Prop} (hG : ∀ i, G i ∈ 𝒢) {t : ℕ} (h : ∀ s < t, ¬ Broadcasts G s) :
    t ≤ advBroadcastTime 𝒢 := by
  have hbdd : BddAbove (Set.range fun G : {G : ℕ → α → α → Prop // ∀ i, G i ∈ 𝒢} =>
      broadcastTime G.1) :=
    ⟨T, by rintro _ ⟨G, rfl⟩; exact broadcastTime_le (hT G.1 G.2)⟩
  exact (le_broadcastTime ⟨T, hT G hG⟩ h).trans
    (le_ciSup (f := fun G : {G : ℕ → α → α → Prop // ∀ i, G i ∈ 𝒢} => broadcastTime G.1) hbdd
      ⟨G, hG⟩)

end Cslib.DynNet
