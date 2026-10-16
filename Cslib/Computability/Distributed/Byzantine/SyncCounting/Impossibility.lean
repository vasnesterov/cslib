/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.SyncCounting.Model
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF

/-!
# Impossibility of synchronous counting with `n ≤ 3 f`

There is no synchronous `c`-counter (`c ≥ 2`) on `3` nodes tolerating `1` Byzantine fault, and more
generally none on `n` nodes tolerating `f` faults whenever `3 ≤ n ≤ 3 f`. This is the classical
bound `f < n / 3` used e.g. by Lenzen, Rybicki and Suomela [LenzenRybickiSuomela2015] and by
Dolev and Hoch, *On self-stabilizing synchronous actions despite Byzantine attacks* (2007).

## Proof (covering / "infinite line" argument, à la Fischer–Lynch–Merritt)

Partition the nodes into three nonempty groups `κ : V → Fin 3` with at most `f` nodes each. Place a
copy of group `p mod 3` at every integer position `p` of the line `ℤ`, and let a node at position
`p` hear the copy of each group nearest to `p` (positions `p - 1`, `p`, `p + 1`): this is the
*line execution* `line A κ ι` from the initial states `ι : ℤ → V → X`.

* Any two adjacent positions `p, p + 1` see exactly what they would see in a genuine execution of
  `A` in which the group at position `p + 2` (equivalently `p - 1`) is Byzantine (`isExec_pair`).
  Hence, if `A` stabilises within `T` rounds, the outputs at positions `p` and `p + 1` agree at
  time `T`, and so all positions of the line have the same output at time `T`.
* The line execution is local: the state at position `p` at time `t` depends only on the initial
  states in `[p - t, p + t]` (`line_congr`), and it is a fault-free run if the initial state is
  the same everywhere (`line_const`).
* Start from a fault-free run `ξ` and put `ξ_T` on the negative half-line and `ξ_{T+1}` on the
  nonnegative one. Far on the left, at time `T`, the line looks like `ξ_{2T}`, far on the right
  like `ξ_{2T+1}`; their (stabilised) outputs differ by one modulo `c ≥ 2`. Contradiction.

## Main results

* `not_isCounter_of_partition`: the core statement for a partition into three groups.
* `not_isCounter_of_card_eq_three`: no counter on `3` nodes with resilience `1`.
* `not_isCounter_of_three_le_card`: no counter on `n` nodes with resilience `f` if `3 ≤ n ≤ 3 f`.

## References

* [C. Lenzen, J. Rybicki, J. Suomela, *Towards optimal synchronous
  counting*][LenzenRybickiSuomela2015]
-/

@[expose] public section

namespace Cslib.Byzantine.SyncCounting

namespace LineExec

/-- The position nearest to `p` (in `{p - 1, p, p + 1}`) that hosts group `k`, i.e. is congruent
to `k` modulo `3`. -/
def nb (p : ℤ) (k : Fin 3) : ℤ := p + ((((k : ℕ) : ℤ) - p + 1) % 3) - 1

lemma nb_emod (p : ℤ) (k : Fin 3) : nb p k % 3 = ((k : ℕ) : ℤ) := by
  have := k.isLt; unfold nb; omega

lemma nb_ge (p : ℤ) (k : Fin 3) : p - 1 ≤ nb p k := by
  unfold nb; omega

lemma nb_le (p : ℤ) (k : Fin 3) : nb p k ≤ p + 1 := by
  unfold nb; omega

lemma nb_eq {p q : ℤ} {k : Fin 3} (hq : q % 3 = ((k : ℕ) : ℤ)) (h1 : p - 1 ≤ q)
    (h2 : q ≤ p + 1) : nb p k = q := by
  unfold nb; omega

variable {V X : Type*} {c : ℕ} (A : Algorithm V X c) (κ : V → Fin 3)

/-- The execution of `A` on the infinite line: position `p` hosts group `p mod 3` (the states of
the other nodes at position `p` are irrelevant), and a node at position `p` receives the state of
node `w` from the nearest position hosting the group of `w`. -/
def line (ι : ℤ → V → X) : ℕ → ℤ → V → X
  | 0 => ι
  | t + 1 => fun p v => A.g v (fun w => line ι t (nb p (κ w)) w)

/-- Locality of the line execution. -/
lemma line_congr {ι ι' : ℤ → V → X} :
    ∀ (t : ℕ) (p : ℤ), (∀ q, p - t ≤ q → q ≤ p + t → ι q = ι' q) →
      line A κ ι t p = line A κ ι' t p
  | 0, p, h => by simpa [line] using h p (by simp) (by simp)
  | t + 1, p, h => by
    funext v
    simp only [line]
    congr 1
    funext w
    have h1 := nb_ge p (κ w)
    have h2 := nb_le p (κ w)
    rw [line_congr t _ (fun q hq1 hq2 => h q (by push_cast; omega) (by push_cast; omega))]

/-- With the same initial state everywhere, the line execution is a fault-free run. -/
lemma line_const (z : V → X) : ∀ (t : ℕ) (p : ℤ), line A κ (fun _ => z) t p = run A z t
  | 0, _ => rfl
  | t + 1, p => by
    funext v
    simp only [line, line_const z t]
    rfl

/-- Two adjacent positions `p, p + 1` of the line (together with the group at `p + 2`, playing the
Byzantine group `k`) form a genuine execution of `A`. -/
lemma isExec_pair [Fintype V] (ι : ℤ → V → X) (p : ℤ) (k : Fin 3)
    (hk : ((k : ℕ) : ℤ) = (p + 2) % 3) :
    IsExec A (Finset.univ.filter (fun v => κ v = k))
      (fun t v => line A κ ι t (nb (p + 1) (κ v)) v) := by
  intro t v hv
  refine ⟨fun w => line A κ ι t (nb (nb (p + 1) (κ v)) (κ w)) w, ?_, rfl⟩
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hw
  have hv' : ((κ v : ℕ) : ℤ) ≠ (k : ℕ) := fun h => hv (Fin.ext (by exact_mod_cast h))
  have hw' : ((κ w : ℕ) : ℤ) ≠ (k : ℕ) := fun h => hw (Fin.ext (by exact_mod_cast h))
  have a1 := nb_ge (p + 1) (κ v)
  have a2 := nb_le (p + 1) (κ v)
  have a3 := nb_emod (p + 1) (κ v)
  have b1 := nb_ge (p + 1) (κ w)
  have b2 := nb_le (p + 1) (κ w)
  have b3 := nb_emod (p + 1) (κ w)
  simp only
  rw [nb_eq b3 (by omega) (by omega)]

end LineExec

open LineExec

/-- The fault-free run is a semigroup action of `ℕ`. -/
lemma run_add {V X : Type*} {c : ℕ} (A : Algorithm V X c) (z : V → X) (a : ℕ) :
    ∀ b, run A z (a + b) = run A (run A z a) b
  | 0 => rfl
  | b + 1 => by
    change run A z (a + b + 1) = _
    simp only [run, run_add A z a b]

private lemma mod_ne_succ_mod {a c : ℕ} (hc : 2 ≤ c) : a % c ≠ (a + 1) % c := by
  intro h
  have h' : a + 0 ≡ a + 1 [MOD c] := h
  have := Nat.ModEq.add_left_cancel' a h'
  unfold Nat.ModEq at this
  rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at this
  exact absurd this (by norm_num)

variable {V X : Type*} [Fintype V] {c : ℕ}

/-- **Core impossibility.** If the nodes can be partitioned into three nonempty groups of at most
`f` nodes each, then no algorithm is a synchronous `c`-counter (`c ≥ 2`) with resilience `f`. -/
theorem not_isCounter_of_partition [Nonempty X] (hc : 2 ≤ c) (A : Algorithm V X c)
    (κ : V → Fin 3) (hκ : Function.Surjective κ) {f : ℕ}
    (hf : ∀ k, (Finset.univ.filter (fun v => κ v = k)).card ≤ f) (T : ℕ) :
    ¬ IsCounter A f T := by
  intro hA
  obtain ⟨z₀⟩ : Nonempty (V → X) := inferInstance
  -- the fault-free run and its stabilisation
  obtain ⟨v₀, hv₀⟩ := hA ∅ (by simp) (run A z₀) (isExec_run A z₀ ∅)
  -- representatives of the groups
  let s : Fin 3 → V := Function.surjInv hκ
  have hs : ∀ k, κ (s k) = k := Function.surjInv_eq hκ
  let fin3 : ℤ → Fin 3 := fun p => ⟨(p % 3).toNat, by omega⟩
  have hfin3 : ∀ p, (((fin3 p : ℕ)) : ℤ) = p % 3 := fun p => by simp only [fin3]; omega
  let rep : ℤ → V := fun p => s (fin3 p)
  have hrep : ∀ p, (((κ (rep p) : ℕ)) : ℤ) = p % 3 := fun p => by simp only [rep, hs, hfin3]
  -- the line execution
  let ι : ℤ → V → X := fun p => if p < 0 then run A z₀ T else run A z₀ (T + 1)
  let O : ℤ → Fin c := fun p => A.h (rep p) (line A κ ι T p (rep p))
  -- adjacent positions agree
  have step : ∀ p, O p = O (p + 1) := by
    intro p
    have hk := hfin3 (p + 2)
    have hE := hA _ (hf (fin3 (p + 2))) _ (isExec_pair A κ ι p (fin3 (p + 2)) hk)
    have hne : ∀ q, (q = p ∨ q = p + 1) → rep q ∉ Finset.univ.filter (fun v => κ v = fin3 (p + 2))
      := by
      intro q hq hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have h1 := hrep q
      rw [hmem, hk] at h1
      omega
    have := hE.out_eq le_rfl (hne p (Or.inl rfl)) (hne (p + 1) (Or.inr rfl))
    have e1 : nb (p + 1) (κ (rep p)) = p := nb_eq (hrep p).symm (by omega) (by omega)
    have e2 : nb (p + 1) (κ (rep (p + 1))) = p + 1 :=
      nb_eq (hrep (p + 1)).symm (by omega) (by omega)
    simp only [e1, e2] at this
    exact this
  have chain : ∀ a : ℤ, ∀ n : ℕ, O a = O (a + n) := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih => rw [ih, step]; push_cast; ring_nf
  have hall := chain (-(T + 1 : ℤ)) (2 * T + 1)
  -- far left
  have hL : line A κ ι T (-(T + 1 : ℤ)) = run A z₀ (T + T) := by
    rw [line_congr A κ (ι' := fun _ => run A z₀ T) T _
      (fun q _ hq => by simp [ι, show q < 0 by omega]), line_const, run_add]
  -- far right
  have hR : line A κ ι T (-(T + 1 : ℤ) + ((2 * T + 1 : ℕ) : ℤ)) = run A z₀ (T + (T + 1)) := by
    rw [line_congr A κ (ι' := fun _ => run A z₀ (T + 1)) T _
      (fun q hq _ => by simp [ι, show ¬ q < 0 by push_cast at hq; omega]), line_const,
      ← run_add, Nat.add_comm (T + 1) T]
  simp only [O, hL, hR] at hall
  have l := hv₀ T (rep (-(T + 1 : ℤ))) (Finset.notMem_empty _)
  have r := hv₀ (T + 1) (rep (-(T + 1 : ℤ) + ((2 * T + 1 : ℕ) : ℤ))) (Finset.notMem_empty _)
  have := congrArg (fun x : Fin c => (x : ℕ)) hall
  rw [l, r] at this
  exact mod_ne_succ_mod (a := v₀ + T) hc (by rw [this]; ring_nf)

/-- **No synchronous counting with `3` nodes and `1` Byzantine fault**: for any algorithm on a
three-element node set, any nonempty state set and `c ≥ 2`, `A` is not a `c`-counter with
resilience `1` (for any stabilisation time `T`). -/
theorem not_isCounter_of_card_eq_three [Nonempty X] (hV : Fintype.card V = 3) (hc : 2 ≤ c)
    (A : Algorithm V X c) (T : ℕ) : ¬ IsCounter A 1 T := by
  classical
  let e : V ≃ Fin 3 := Fintype.equivFinOfCardEq hV
  refine not_isCounter_of_partition hc A e e.surjective (fun k => ?_) T
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact e.injective (ha.trans hb.symm)

/-- **The `n ≤ 3 f` bound**: if `3 ≤ n ≤ 3 f`, there is no synchronous `c`-counter (`c ≥ 2`) on
`n` nodes with resilience `f`. -/
theorem not_isCounter_of_three_le_card [Nonempty X] {f : ℕ} (h3 : 3 ≤ Fintype.card V)
    (hf : Fintype.card V ≤ 3 * f) (hc : 2 ≤ c) (A : Algorithm V X c) (T : ℕ) :
    ¬ IsCounter A f T := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let κ : V → Fin 3 := fun v => ⟨(e v : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩
  have hκ : Function.Surjective κ := by
    intro k
    refine ⟨e.symm ⟨k, by omega⟩, Fin.ext ?_⟩
    simp only [κ, Equiv.apply_symm_apply]
    exact Nat.mod_eq_of_lt k.isLt
  refine not_isCounter_of_partition hc A κ hκ (fun k => ?_) T
  calc (Finset.univ.filter (fun v => κ v = k)).card ≤ (Finset.range f).card := by
        refine Finset.card_le_card_of_injOn (fun v => (e v : ℕ) / 3) ?_ ?_
        · intro v _
          simp only [Finset.coe_range, Set.mem_Iio]
          have := (e v).isLt
          omega
        · intro a ha b hb hab
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, κ,
            Fin.ext_iff] at ha hb hab
          apply e.injective
          ext
          omega
    _ = f := Finset.card_range f

end Cslib.Byzantine.SyncCounting
