/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.Congest.LowerBound
public import Mathlib.Basic.Real.Basic

/-!
# Randomized CONGEST algorithms and private-coin protocols (Theorem 1.1, randomized half)


* A **randomized CONGEST algorithm** is a deterministic `Algorithm V (I × ρ) σ B` whose node `v`
  additionally receives its own private random string `r v : ρ`; `r : V → ρ` is uniform
  (counting measure). `RandDecides A G inp T f ε`: for every input, the set of random strings on
  which "all nodes accept" differs from `f x y` has density at most `ε`.
* A **private-coin randomized protocol** is a deterministic protocol on inputs `(x, r_A)` and
  `(y, r_B)` with uniform coins `r_A : R_A`, `r_B : R_B` (`Protocol.RandComputes`).
* `LBFamily.rand_simulation`: a randomized algorithm on a family of lower bound graphs yields a
  private-coin protocol with the same error and `T · 2 · |Ecut| · B + 2` bits (Alice draws the
  random strings of `V_A`, Bob those of `V_B`).
* `LBFamily.rand_lowerBound`: hence `CC^R_ε(f) ≤ T · 2 · |Ecut| · B + 2`. The randomized lower bound
  `CC^R(DISJ_K) = Ω(K)` (Kalyanasundaram–Schnitger, Razborov) is **not** formalized; it enters as
  the hypothesis `hC`.
-/

@[expose] public section

namespace Cslib.CommunicationComplexity.Protocol

open Finset

variable {X Y RA RB : Type*} [Fintype RA] [Fintype RB]

/-- Number of coin pairs on which the protocol errs. -/
noncomputable def errCount (P : Protocol (X × RA) (Y × RB) Bool) (f : X → Y → Bool) (x : X)
    (y : Y) : ℕ := by
  classical
  exact (univ.filter fun r : RA × RB => P.eval (x, r.1) (y, r.2) ≠ f x y).card

/-- A private-coin randomized protocol computing `f` with error at most `ε` on every input. -/
def RandComputes (P : Protocol (X × RA) (Y × RB) Bool) (f : X → Y → Bool) (ε : ℝ) : Prop :=
  ∀ x y, (P.errCount f x y : ℝ) ≤ ε * (Fintype.card RA * Fintype.card RB)

end Cslib.CommunicationComplexity.Protocol

namespace Cslib.Congest

open Cslib.CommunicationComplexity

open Finset

namespace LBFamily

open Protocol

variable {X Y V I σ ρ : Type*} {B : ℕ} [Fintype V] [DecidableEq V] [Fintype ρ]

/-- Number of random strings on which a randomized algorithm errs. -/
noncomputable def Algorithm.randErr (A : Algorithm V (I × ρ) σ B) (G : SimpleGraph V)
    [DecidableRel G.Adj] (inp : V → I) (T : ℕ) (b : Bool) : ℕ := by
  classical
  exact (univ.filter fun r : V → ρ =>
    decide (A.Accepts G (fun v => (inp v, r v)) T) ≠ b).card

variable (F : LBFamily X Y V I) [∀ x y, DecidableRel (F.G x y).Adj]

/-- Combine Alice's and Bob's random strings into one random string for all nodes. -/
def combine (rA : {v // F.alice v = true} → ρ) (rB : {v // F.alice v = false} → ρ) : V → ρ :=
  fun v => if h : F.alice v = true then rA ⟨v, h⟩ else rB ⟨v, by simpa using h⟩

/-- `combine` is a bijection. -/
def combineEquiv : ({v // F.alice v = true} → ρ) × ({v // F.alice v = false} → ρ) ≃ (V → ρ) where
  toFun p := F.combine p.1 p.2
  invFun r := (fun v => r v, fun v => r v)
  left_inv p := by
    obtain ⟨rA, rB⟩ := p
    ext ⟨v, hv⟩
    · simp [combine, hv]
    · have : ¬F.alice v = true := by simp [hv]
      simp [combine, this]
  right_inv r := by
    funext v
    by_cases h : F.alice v = true <;> simp [combine, h]

/-- The family with each node's random string added to its input; Alice's input is
`(x, r_A)`, Bob's is `(y, r_B)`. -/
def withCoins : LBFamily (X × ({v // F.alice v = true} → ρ)) (Y × ({v // F.alice v = false} → ρ))
    V (I × ρ) where
  G xr yr := F.G xr.1 yr.1
  inp xr yr v := (F.inp xr.1 yr.1 v, F.combine xr.2 yr.2 v)
  alice := F.alice
  Ecut := F.Ecut
  Ecut_sub := F.Ecut_sub
  adj_cut xr yr := F.adj_cut xr.1 yr.1
  adj_alice xr yr yr' := F.adj_alice xr.1 yr.1 yr'.1
  adj_bob xr xr' yr := F.adj_bob xr.1 xr'.1 yr.1
  adj_fixed xr xr' yr yr' := F.adj_fixed xr.1 xr'.1 yr.1 yr'.1
  inp_alice xr yr yr' v hv := by
    simp only [Prod.mk.injEq]
    exact ⟨F.inp_alice _ _ _ v hv, by simp [combine, hv]⟩
  inp_bob xr xr' yr v hv := by
    simp only [Prod.mk.injEq]
    have : ¬F.alice v = true := by simp [hv]
    exact ⟨F.inp_bob _ _ _ v hv, by simp [combine, this]⟩

/-- Adjacency in the family with coins is adjacency in the original family. -/
instance (xr : X × ({v // F.alice v = true} → ρ)) (yr : Y × ({v // F.alice v = false} → ρ)) :
    DecidableRel ((F.withCoins (ρ := ρ)).G xr yr).Adj :=
  inferInstanceAs (DecidableRel (F.G xr.1 yr.1).Adj)

/-- **Simulation, randomized** (Theorem 1.1): a randomized `T`-round algorithm with `B`-bit messages
on a family of lower bound graphs yields a private-coin protocol with at most
`T · 2 · |Ecut| · B + 2` bits whose number of bad coin pairs on `(x, y)` equals the number of bad
random strings of the algorithm on `G x y`. -/
theorem rand_simulation [Nonempty X] [Nonempty Y] [Nonempty ρ] (A : Algorithm V (I × ρ) σ B)
    (T : ℕ) (f : X → Y → Bool) :
    ∃ P : Protocol (X × ({v // F.alice v = true} → ρ)) (Y × ({v // F.alice v = false} → ρ)) Bool,
      P.CostLE (T * (2 * (F.Ecut.card * B)) + 2) ∧
      ∀ x y, P.errCount f x y = Algorithm.randErr A (F.G x y) (F.inp x y) T (f x y) := by
  classical
  obtain ⟨P, hc, hP⟩ := (F.withCoins (ρ := ρ)).simulation A T
  refine ⟨P, by simpa [withCoins] using hc, fun x y => ?_⟩
  simp only [errCount, Algorithm.randErr]
  rw [← card_map (F.combineEquiv (ρ := ρ)).toEmbedding]
  congr 1
  ext r
  simp only [mem_map_equiv, mem_filter, mem_univ, true_and]
  rw [hP]
  have e : F.combine (F.combineEquiv.symm r).1 (F.combineEquiv.symm r).2 = r :=
    F.combineEquiv.apply_symm_apply r
  change decide (A.Accepts (F.G x y) (fun v => (F.inp x y v, F.combine (F.combineEquiv.symm r).1
    (F.combineEquiv.symm r).2 v)) T) ≠ f x y ↔ _
  rw [e]

/-- **Theorem 1.1 (randomized).** If every private-coin protocol computing `f` with error `≤ ε`
needs `C` bits, and a randomized algorithm decides `f` on the family with error `≤ ε` in `T`
rounds, then `C ≤ T · 2 · |Ecut| · B + 2`. -/
theorem rand_lowerBound [Nonempty X] [Nonempty Y] [Nonempty ρ] (A : Algorithm V (I × ρ) σ B)
    (T : ℕ) (f : X → Y → Bool) (ε : ℝ)
    (hA : ∀ x y, (Algorithm.randErr A (F.G x y) (F.inp x y) T (f x y) : ℝ) ≤
      ε * Fintype.card (V → ρ))
    (C : ℕ)
    (hC : ∀ (P : Protocol (X × ({v // F.alice v = true} → ρ))
      (Y × ({v // F.alice v = false} → ρ)) Bool) (c : ℕ),
      P.RandComputes f ε → P.CostLE c → C ≤ c) :
    C ≤ T * (2 * (F.Ecut.card * B)) + 2 := by
  obtain ⟨P, hc, hP⟩ := F.rand_simulation A T f
  refine hC P _ (fun x y => ?_) hc
  rw [hP x y]
  have hcard : (Fintype.card ({v // F.alice v = true} → ρ) : ℝ) *
      Fintype.card ({v // F.alice v = false} → ρ) = Fintype.card (V → ρ) := by
    rw [← Nat.cast_mul, ← Fintype.card_prod, Fintype.card_congr (F.combineEquiv (ρ := ρ))]
  rw [hcard]
  exact hA x y

end LBFamily

end Cslib.Congest
