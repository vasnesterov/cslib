/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Local.LocallyIterative
public import Cslib.Foundations.Data.Nat.LogStar
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.Algebra.Field.ZMod

/-!
# Linial's `O(Δ²)`-colouring as a locally-iterative algorithm

Linial's colour reduction [Linial, *Locality in distributed graph algorithms*, SICOMP 1992], in the
algebraic (polynomial) form: with a prime `q` and a degree bound `d`, the colour `x < q ^ (d + 1)`
is identified with the polynomial `P_x ∈ 𝔽_q[X]` of degree `≤ d` whose coefficients are the base-`q`
digits of `x`. Two distinct such polynomials agree on at most `d` points, so if `d * Δ < q`, a
vertex with at most `Δ` neighbours finds a point `a ∈ 𝔽_q` with `P_x(a) ≠ P_y(a)` for every
neighbouring colour `y`; its new colour is the pair `(a, P_x(a))`, encoded as `a * q + P_x(a) < q²`.
The new colouring is proper. The new colour depends only on the own colour and the **set** of
neighbouring colours, so this is a locally-iterative (SET-LOCAL) algorithm.

Iteration: in round `t` the current palette size `palette n Δ t` is common knowledge (it depends
only on the initial palette size `n`, on `Δ` and on `t`); the round uses the least prime `q` for
which some `d` is admissible (`d * Δ < q`, `palette ≤ q ^ (d + 1)`). Bertrand's postulate gives
the bounds `m ↦ (2KΔ)²` for `m ≤ (Δ+1)^K` (logarithmic phase, `log* n` rounds) and then three
rounds with `d = 11, 3, 2` reach the palette `max (16 Δ²) 256`.

## Main definitions

* `Linial.poly q d x` — the polynomial of the colour `x`.
* `Linial.reduce q d x N` — one reduction round (least separating point, classical choice).
* `Linial.palette n Δ t` — the palette size after `t` rounds.
* `linial n Δ` — Linial's algorithm for initial palette `n` and maximum degree `Δ`.

## Main results

* `Linial.isProper_reduce`, `Linial.reduce_lt` — one round keeps properness, colours `< q²`.
* `linial_isProper` — every round of `linial n Δ` is a proper colouring.
* `linial_lt` — for `Δ ≥ 1`, after `log* n + 3` rounds all colours are `< max (16 Δ²) 256`;
  `linial_lt_sixteen_mul_sq`: `< 16 Δ²` when `Δ ≥ 4`.
-/

@[expose] public section

open Polynomial

namespace Cslib.LocallyIterative

namespace Linial

/-- The `i`-th base-`q` digit of `x`. -/
def digit (q i x : ℕ) : ℕ := x / q ^ i % q

theorem mod_pow_eq_of_digit_eq {q x y : ℕ} {k : ℕ} (h : ∀ i < k, digit q i x = digit q i y) :
    x % q ^ k = y % q ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ih (fun i hi => h i (by omega))]
    simp only [digit] at h
    rw [h k (by omega)]

/-- The polynomial of degree `≤ d` over `ZMod q` whose coefficients are the first `d + 1`
base-`q` digits of `x`. -/
noncomputable def poly (q d x : ℕ) : (ZMod q)[X] :=
  ∑ i ∈ Finset.range (d + 1), C ((digit q i x : ℕ) : ZMod q) * X ^ i

theorem coeff_poly (q d x i : ℕ) :
    (poly q d x).coeff i = if i < d + 1 then ((digit q i x : ℕ) : ZMod q) else 0 := by
  simp [poly]

theorem natDegree_poly_le (q d x : ℕ) : (poly q d x).natDegree ≤ d := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  simp [coeff_poly, show ¬ i < d + 1 by omega]

theorem poly_injective {q d x y : ℕ} (hq : 0 < q) (hx : x < q ^ (d + 1)) (hy : y < q ^ (d + 1))
    (h : poly q d x = poly q d y) : x = y := by
  have hd : ∀ i < d + 1, digit q i x = digit q i y := by
    intro i hi
    have := congrArg (fun p => p.coeff i) h
    simp only [coeff_poly, hi, ite_true] at this
    have h1 : digit q i x < q := Nat.mod_lt _ hq
    have h2 : digit q i y < q := Nat.mod_lt _ hq
    rw [ZMod.natCast_eq_natCast_iff'] at this
    rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  have := mod_pow_eq_of_digit_eq hd
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

/-- The evaluation point `a` *separates* the colour `x` from the colours in `N`: `a < q` and `P_x`
differs from every `P_y`, `y ∈ N`, at `a`. -/
def Separates (q d x : ℕ) (N : Set ℕ) (a : ℕ) : Prop :=
  a < q ∧ ∀ y ∈ N, (poly q d x).eval (a : ZMod q) ≠ (poly q d y).eval (a : ZMod q)

/-- Pigeonhole: if `d * Δ < q`, then for at most `Δ` other colours below `q ^ (d + 1)` there is a
separating evaluation point (two distinct polynomials of degree `≤ d` agree on at most `d`
points). -/
theorem exists_separates {q d Δ x : ℕ} {N : Set ℕ} (hq : q.Prime) (hdq : d * Δ < q)
    (hx : x < q ^ (d + 1)) (hN : N.Finite) (hNcard : N.ncard ≤ Δ)
    (hNlt : ∀ y ∈ N, y < q ^ (d + 1)) (hxN : x ∉ N) : ∃ a, Separates q d x N a := by
  have := Fact.mk hq
  classical
  set B : Finset (ZMod q) :=
    hN.toFinset.biUnion (fun y => (poly q d x - poly q d y).roots.toFinset) with hBdef
  have hB : B.card < q := by
    calc B.card ≤ ∑ y ∈ hN.toFinset, (poly q d x - poly q d y).roots.toFinset.card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ hN.toFinset, d := Finset.sum_le_sum fun y _ =>
          (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ((natDegree_sub_le _ _).trans
            (max_le (natDegree_poly_le ..) (natDegree_poly_le ..))))
      _ = hN.toFinset.card * d := by simp
      _ ≤ Δ * d := Nat.mul_le_mul_right _ (by rwa [← Set.ncard_eq_toFinset_card N hN])
      _ < q := by rwa [mul_comm]
  obtain ⟨z, hz⟩ : ∃ z : ZMod q, z ∉ B := by
    by_contra h
    push Not at h
    have := Finset.card_le_card (fun z (_ : z ∈ (Finset.univ : Finset (ZMod q))) => h z)
    simp [ZMod.card] at this
    omega
  refine ⟨z.val, ZMod.val_lt z, fun y hy he => hz ?_⟩
  rw [ZMod.natCast_zmod_val] at he
  simp only [B, Finset.mem_biUnion, Set.Finite.mem_toFinset, Multiset.mem_toFinset]
  refine ⟨y, hy, ?_⟩
  rw [mem_roots (sub_ne_zero.2 fun h => hxN (poly_injective hq.pos hx (hNlt y hy) h ▸ hy)),
    IsRoot, eval_sub, he, sub_self]

/-- The new colour of a vertex with colour `x` using evaluation point `a`: the pair
`(a, P_x(a))` encoded as `a * q + P_x(a)`. -/
noncomputable def code (q d x a : ℕ) : ℕ := a * q + ((poly q d x).eval (a : ZMod q)).val

theorem code_lt {q d x a : ℕ} (hq : 0 < q) (ha : a < q) : code q d x a < q ^ 2 := by
  have : NeZero q := ⟨hq.ne'⟩
  have := ZMod.val_lt ((poly q d x).eval (a : ZMod q))
  unfold code
  nlinarith

theorem eval_eq_of_code_eq {q d x y a b : ℕ} (hq : 0 < q) (h : code q d x a = code q d y b) :
    a = b ∧ (poly q d x).eval (a : ZMod q) = (poly q d y).eval (b : ZMod q) := by
  have : NeZero q := ⟨hq.ne'⟩
  have hx := ZMod.val_lt ((poly q d x).eval (a : ZMod q))
  have hy := ZMod.val_lt ((poly q d y).eval (b : ZMod q))
  unfold code at h
  have h1 := congrArg (· / q) h
  have h2 := congrArg (· % q) h
  simp only [Nat.mul_comm _ q, Nat.mul_add_div hq, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h1 h2
  exact ⟨by simpa using h1, ZMod.val_injective _ h2⟩

open Classical in
/-- **One round of Linial's colour reduction** with prime field size `q` and degree bound `d`:
a vertex with colour `x` whose neighbours have the colours `N` picks the least separating point
`a` and takes the colour `a * q + P_x(a) < q ^ 2`. (If no separating point exists, which does
not happen under the hypotheses of `isProper_reduce`, it takes the colour `0`.) -/
noncomputable def reduce (q d x : ℕ) (N : Set ℕ) : ℕ :=
  if h : ∃ a, Separates q d x N a then code q d x (Nat.find h) else 0

theorem reduce_eq_code {q d x : ℕ} {N : Set ℕ} (h : ∃ a, Separates q d x N a) :
    ∃ a, Separates q d x N a ∧ reduce q d x N = code q d x a := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, by simp only [reduce, h, dite_true]⟩

section Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {Δ q d : ℕ}

theorem exists_separates_nbrColors (hq : q.Prime) (hdq : d * Δ < q)
    (hdeg : ∀ v, G.degree v ≤ Δ) {c : V → ℕ} (hc : IsProper G c) (hlt : ∀ v, c v < q ^ (d + 1))
    (v : V) : ∃ a, Separates q d (c v) (nbrColors G c v) a := by
  refine exists_separates hq hdq (hlt v) (finite_nbrColors c v)
    ((ncard_nbrColors_le c v).trans (hdeg v)) ?_ ?_
  · rintro _ ⟨u, -, rfl⟩
    exact hlt u
  · rintro ⟨u, hu, he⟩
    exact hc hu he.symm

/-- One reduction round keeps a proper colouring proper. -/
theorem isProper_reduce (hq : q.Prime) (hdq : d * Δ < q) (hdeg : ∀ v, G.degree v ≤ Δ)
    {c : V → ℕ} (hc : IsProper G c) (hlt : ∀ v, c v < q ^ (d + 1)) :
    IsProper G (fun v => reduce q d (c v) (nbrColors G c v)) := by
  intro u v huv he
  obtain ⟨a, ⟨-, hau⟩, hu⟩ := reduce_eq_code (exists_separates_nbrColors hq hdq hdeg hc hlt u)
  obtain ⟨b, -, hv⟩ := reduce_eq_code (exists_separates_nbrColors hq hdq hdeg hc hlt v)
  simp only [hu, hv] at he
  obtain ⟨rfl, he⟩ := eval_eq_of_code_eq hq.pos he
  exact hau (c v) (mem_nbrColors_of_adj c huv) he

/-- After one reduction round all colours are `< q ^ 2`. -/
theorem reduce_lt (hq : q.Prime) (hdq : d * Δ < q) (hdeg : ∀ v, G.degree v ≤ Δ)
    {c : V → ℕ} (hc : IsProper G c) (hlt : ∀ v, c v < q ^ (d + 1)) (v : V) :
    reduce q d (c v) (nbrColors G c v) < q ^ 2 := by
  obtain ⟨a, ⟨ha, -⟩, hv⟩ := reduce_eq_code (exists_separates_nbrColors hq hdq hdeg hc hlt v)
  rw [hv]
  exact code_lt hq.pos ha

end Graph

@[deprecated (since := "2026-10-18")] alias lt_tower_logStar_succ := Nat.lt_tower_logStar_succ
@[deprecated (since := "2026-10-18")] alias clog_le_tower_logStar := Nat.clog_le_tower_logStar

/-! ### Choosing the parameters -/

/-- The pair `(q, d)` is *admissible* for palette size `m` and maximum degree `Δ`: `q` is prime,
`d * Δ < q` and `m ≤ q ^ (d + 1)` (every colour `< m` has a polynomial of degree `≤ d`). -/
def Admissible (Δ m q d : ℕ) : Prop := q.Prime ∧ d * Δ < q ∧ m ≤ q ^ (d + 1)

theorem exists_admissible (Δ m : ℕ) : ∃ q d, Admissible Δ m q d := by
  obtain ⟨p, hmp, hp⟩ := Nat.exists_infinite_primes m
  exact ⟨p, 0, hp, by simpa using hp.pos, by simpa using hmp⟩

open Classical in
/-- The field size used on palette size `m`: the least prime `q` admitting a degree. -/
noncomputable def fieldSize (Δ m : ℕ) : ℕ := Nat.find (exists_admissible Δ m)

open Classical in
/-- The degree bound used on palette size `m` (the least one admissible with `fieldSize Δ m`). -/
noncomputable def polyDegree (Δ m : ℕ) : ℕ := Nat.find (Nat.find_spec (exists_admissible Δ m))

theorem admissible_fieldSize (Δ m : ℕ) : Admissible Δ m (fieldSize Δ m) (polyDegree Δ m) := by
  classical
  exact Nat.find_spec (Nat.find_spec (exists_admissible Δ m))

theorem fieldSize_le {Δ m q d : ℕ} (h : Admissible Δ m q d) : fieldSize Δ m ≤ q := by
  classical
  exact Nat.find_min' _ ⟨d, h⟩

/-- Bertrand's postulate gives an admissible prime in `(N, 2N]`. -/
theorem fieldSize_le_two_mul {Δ m d N : ℕ} (hN : N ≠ 0) (hdN : d * Δ ≤ N)
    (hm : m ≤ (N + 1) ^ (d + 1)) : fieldSize Δ m ≤ 2 * N := by
  obtain ⟨p, hp, hNp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul N hN
  exact (fieldSize_le ⟨hp, by omega, hm.trans (Nat.pow_le_pow_left hNp _)⟩).trans hp2

/-- The palette size after `t` rounds, starting from `n` colours. It depends only on `n`, `Δ`
and `t`, so every vertex knows it. -/
noncomputable def palette (n Δ : ℕ) : ℕ → ℕ
  | 0 => n
  | t + 1 => fieldSize Δ (palette n Δ t) ^ 2

/-! ### The algorithm -/

end Linial

/-- **Linial's colour reduction** as a locally-iterative algorithm, for initial palette size `n`
and maximum degree `Δ`: in round `t`, with current palette size `m = palette n Δ t`, perform one
reduction round with the least admissible prime `q` and degree `d` for `m` (`Linial.reduce`). -/
noncomputable def linial (n Δ : ℕ) : Algorithm ℕ :=
  ⟨fun t => Linial.reduce (Linial.fieldSize Δ (Linial.palette n Δ t))
    (Linial.polyDegree Δ (Linial.palette n Δ t))⟩

namespace Linial

/-! ### Palette bounds -/

/-- One round from `m ≤ (Δ+1)^K` colours: `m' ≤ (2KΔ)² ≤ (Δ+1)^(4 + 2⌈log₂ K⌉)`. -/
theorem fieldSize_sq_le_of_le_pow {Δ m K : ℕ} (hΔ : 1 ≤ Δ) (hK : 1 ≤ K) (hm : m ≤ (Δ + 1) ^ K) :
    fieldSize Δ m ^ 2 ≤ (Δ + 1) ^ (4 + 2 * Nat.clog 2 K) := by
  have h1 : fieldSize Δ m ≤ 2 * (K * Δ) := by
    refine fieldSize_le_two_mul (d := K - 1) (by positivity) ?_ ?_
    · exact Nat.mul_le_mul_right _ (by omega)
    · rw [show K - 1 + 1 = K by omega]
      exact hm.trans (Nat.pow_le_pow_left (by nlinarith) _)
  have h2 : 2 * (K * Δ) ≤ (Δ + 1) ^ (2 + Nat.clog 2 K) := by
    have hK2 := Nat.le_pow_clog (b := 2) (by norm_num) K
    have : 2 ^ Nat.clog 2 K ≤ (Δ + 1) ^ Nat.clog 2 K := Nat.pow_le_pow_left (by omega) _
    rw [pow_add]
    nlinarith
  calc fieldSize Δ m ^ 2 ≤ ((Δ + 1) ^ (2 + Nat.clog 2 K)) ^ 2 := Nat.pow_le_pow_left (h1.trans h2) _
    _ = (Δ + 1) ^ (4 + 2 * Nat.clog 2 K) := by rw [← pow_mul]; ring_nf

/-- Thresholds for the logarithmic phase: `thr 0 = 12`, `thr (k + 1) = 2 ^ ((thr k - 4) / 2)`.
From palette `≤ (Δ+1)^(thr (k+1))` one round reaches palette `≤ (Δ+1)^(thr k)`. -/
def thr : ℕ → ℕ
  | 0 => 12
  | k + 1 => 2 ^ ((thr k - 4) / 2)

theorem twelve_le_thr : ∀ k, 12 ≤ thr k
  | 0 => le_rfl
  | k + 1 => by
    have := twelve_le_thr k
    calc 12 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ ((thr k - 4) / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem tower_le_thr (k : ℕ) : Nat.tower k ≤ thr k := by
  -- the stronger `2 * tower (k + 2) + 8 ≤ thr (k + 1)` carries the induction
  have key : ∀ k, 2 * Nat.tower (k + 2) + 8 ≤ thr (k + 1) ∧ 4 ≤ Nat.tower (k + 2) := by
    intro k
    induction k with
    | zero => simp [Nat.tower, thr]
    | succ k ih =>
      obtain ⟨ih, h4⟩ := ih
      set t := Nat.tower (k + 2)
      have ht : Nat.tower (k + 3) = 2 ^ t := rfl
      have hthr : thr (k + 2) = 2 ^ ((thr (k + 1) - 4) / 2) := rfl
      rw [ht, hthr]
      have h1 : t + 2 ≤ (thr (k + 1) - 4) / 2 := by omega
      have h2 : 2 ^ (t + 2) ≤ 2 ^ ((thr (k + 1) - 4) / 2) := Nat.pow_le_pow_right (by norm_num) h1
      have h3 : 16 ≤ 2 ^ t := (Nat.pow_le_pow_right (by norm_num) h4 : 2 ^ 4 ≤ 2 ^ t)
      have : 4 ≤ 2 ^ t := by omega
      refine ⟨?_, this⟩
      rw [pow_add] at h2
      omega
  have mono : ∀ k, Nat.tower k ≤ Nat.tower (k + 1) := fun k =>
    (Nat.lt_two_pow_self).le
  rcases k with _ | k
  · simp [Nat.tower, thr]
  · exact (mono _).trans ((Nat.le_mul_of_pos_left _ (by norm_num)).trans
      ((Nat.le_add_right _ 8).trans (key k).1))

theorem fieldSize_sq_le_thr {Δ m k : ℕ} (hΔ : 1 ≤ Δ) (hm : m ≤ (Δ + 1) ^ thr (k + 1)) :
    fieldSize Δ m ^ 2 ≤ (Δ + 1) ^ thr k := by
  refine (fieldSize_sq_le_of_le_pow hΔ (by have := twelve_le_thr (k + 1); omega) hm).trans
    (Nat.pow_le_pow_right (by omega) ?_)
  have := twelve_le_thr k
  rw [show thr (k + 1) = 2 ^ ((thr k - 4) / 2) from rfl, Nat.clog_pow _ _ (by norm_num)]
  omega

/-- After `k` rounds of the logarithmic phase the palette is at most `(Δ + 1) ^ 12`. -/
theorem palette_add_le {n Δ : ℕ} (hΔ : 1 ≤ Δ) :
    ∀ k s, palette n Δ s ≤ (Δ + 1) ^ thr k → palette n Δ (s + k) ≤ (Δ + 1) ^ 12
  | 0, s, h => h
  | k + 1, s, h => by
    rw [show s + (k + 1) = (s + 1) + k by omega]
    exact palette_add_le hΔ k (s + 1) (fieldSize_sq_le_thr hΔ h)

theorem fieldSize_sq_le_484 {Δ m : ℕ} (hΔ : 1 ≤ Δ) (hm : m ≤ (Δ + 1) ^ 12) :
    fieldSize Δ m ^ 2 ≤ 484 * Δ ^ 2 := by
  have : fieldSize Δ m ≤ 2 * (11 * Δ) :=
    fieldSize_le_two_mul (d := 11) (by omega) le_rfl (hm.trans (Nat.pow_le_pow_left (by omega) _))
  nlinarith

theorem fieldSize_sq_le_196 {Δ m : ℕ} (hm : m ≤ 484 * Δ ^ 2) :
    fieldSize Δ m ^ 2 ≤ max (36 * Δ ^ 2) 196 := by
  have : fieldSize Δ m ≤ 2 * max (3 * Δ) 7 := by
    refine fieldSize_le_two_mul (d := 3) (by omega) (le_max_left _ _) (hm.trans ?_)
    have h1 : 3 * Δ + 1 ≤ max (3 * Δ) 7 + 1 := by omega
    have h2 : 8 ≤ max (3 * Δ) 7 + 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h1) (Nat.mul_le_mul h2 h2)
    generalize max (3 * Δ) 7 + 1 = M at *
    rw [show M ^ (3 + 1) = M * M * (M * M) by ring]
    nlinarith
  rcases le_total (3 * Δ) 7 with h | h
  · rw [max_eq_right h] at this; rw [max_eq_right (by nlinarith)]; nlinarith
  · rw [max_eq_left h] at this; rw [max_eq_left (by nlinarith)]; nlinarith

theorem fieldSize_sq_le_256 {Δ m : ℕ} (hm : m ≤ max (36 * Δ ^ 2) 729) :
    fieldSize Δ m ^ 2 ≤ max (16 * Δ ^ 2) 256 := by
  have : fieldSize Δ m ≤ 2 * max (2 * Δ) 8 := by
    refine fieldSize_le_two_mul (d := 2) (by omega) (le_max_left _ _) (hm.trans ?_)
    have h1 : 2 * Δ + 1 ≤ max (2 * Δ) 8 + 1 := by omega
    have h2 : 9 ≤ max (2 * Δ) 8 + 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h1) h2
    have := Nat.mul_le_mul (Nat.mul_le_mul h2 h2) h2
    generalize max (2 * Δ) 8 + 1 = M at *
    rw [show M ^ (2 + 1) = M * M * M by ring]
    refine max_le ?_ ?_ <;> nlinarith
  rcases le_total (2 * Δ) 8 with h | h
  · rw [max_eq_right h] at this; rw [max_eq_right (by nlinarith)]; nlinarith
  · rw [max_eq_left h] at this; rw [max_eq_left (by nlinarith)]; nlinarith

/-- **Palette bound.** For `Δ ≥ 1`, after `log* n + 3` rounds (and in every later round) the
palette size is at most `max (16 Δ²) 256` (i.e. `16 Δ²` for `Δ ≥ 4`). -/
theorem palette_le {n Δ : ℕ} (hΔ : 1 ≤ Δ) {t : ℕ} (ht : Nat.logStar n + 3 ≤ t) :
    palette n Δ t ≤ max (16 * Δ ^ 2) 256 := by
  set L := Nat.logStar n
  have h0 : palette n Δ 0 ≤ (Δ + 1) ^ thr L := by
    calc palette n Δ 0 = n := rfl
      _ ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
      _ ≤ 2 ^ thr L := Nat.pow_le_pow_right (by norm_num)
          ((Nat.clog_le_tower_logStar n).trans (tower_le_thr L))
      _ ≤ (Δ + 1) ^ thr L := Nat.pow_le_pow_left (by omega) _
  have hL := palette_add_le hΔ L 0 h0
  rw [zero_add] at hL
  have hL1 : palette n Δ (L + 1) ≤ 484 * Δ ^ 2 := fieldSize_sq_le_484 hΔ hL
  have hL2 : palette n Δ (L + 2) ≤ max (36 * Δ ^ 2) 729 :=
    (fieldSize_sq_le_196 hL1).trans (max_le_max le_rfl (by norm_num))
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction s with
  | zero => exact fieldSize_sq_le_256 hL2
  | succ s ih =>
    refine fieldSize_sq_le_256 ((ih (by omega)).trans (max_le_max (by nlinarith) (by norm_num)))

section Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {n Δ : ℕ}

/-- Every round of `linial` keeps the colouring proper, and colours stay below the palette size. -/
theorem linial_invariant (hdeg : ∀ v, G.degree v ≤ Δ) {c₀ : V → ℕ} (hc₀ : IsProper G c₀)
    (hlt : ∀ v, c₀ v < n) (t : ℕ) :
    IsProper G ((linial n Δ).run G c₀ t) ∧ ∀ v, (linial n Δ).run G c₀ t v < palette n Δ t := by
  induction t with
  | zero => exact ⟨hc₀, hlt⟩
  | succ t ih =>
    obtain ⟨hq, hdq, hm⟩ := admissible_fieldSize Δ (palette n Δ t)
    have hlt' : ∀ v, (linial n Δ).run G c₀ t v < fieldSize Δ (palette n Δ t) ^
        (polyDegree Δ (palette n Δ t) + 1) := fun v => (ih.2 v).trans_le hm
    exact ⟨isProper_reduce hq hdq hdeg ih.1 hlt', reduce_lt hq hdq hdeg ih.1 hlt'⟩

end Graph

end Linial

open Linial

section Main

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {n Δ : ℕ}

/-- Every round of Linial's algorithm keeps a proper colouring proper. -/
theorem linial_isProper (hdeg : ∀ v, G.degree v ≤ Δ) {c₀ : V → ℕ} (hc₀ : IsProper G c₀)
    (hlt : ∀ v, c₀ v < n) (t : ℕ) : IsProper G ((linial n Δ).run G c₀ t) :=
  (linial_invariant hdeg hc₀ hlt t).1

/-- **Linial's `O(Δ²)`-colouring** [Linial, SICOMP'92], locally-iterative version. On a graph of
maximum degree `Δ ≥ 1`, starting from a proper colouring with colours `< n`, after `log* n + 3`
rounds (and in every later round) all colours are `< max (16 Δ²) 256`. -/
theorem linial_lt (hΔ : 1 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) {c₀ : V → ℕ}
    (hc₀ : IsProper G c₀) (hlt : ∀ v, c₀ v < n) {t : ℕ} (ht : Nat.logStar n + 3 ≤ t) (v : V) :
    (linial n Δ).run G c₀ t v < max (16 * Δ ^ 2) 256 :=
  ((linial_invariant hdeg hc₀ hlt t).2 v).trans_le (palette_le hΔ ht)

/-- `linial_lt` for `Δ ≥ 4`: after `log* n + 3` rounds the colours are `< 16 Δ²`. -/
theorem linial_lt_sixteen_mul_sq (hΔ : 4 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) {c₀ : V → ℕ}
    (hc₀ : IsProper G c₀) (hlt : ∀ v, c₀ v < n) {t : ℕ} (ht : Nat.logStar n + 3 ≤ t) (v : V) :
    (linial n Δ).run G c₀ t v < 16 * Δ ^ 2 := by
  have := linial_lt (by omega) hdeg hc₀ hlt ht v
  rwa [max_eq_left (by nlinarith)] at this

end Main

end Cslib.LocallyIterative
