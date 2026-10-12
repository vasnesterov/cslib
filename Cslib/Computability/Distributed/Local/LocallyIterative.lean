/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Synchronous locally-iterative algorithms (LOCAL / SET-LOCAL model)

A *locally-iterative* algorithm (Szegedy–Vishwanathan, STOC'93) on a graph `G` maintains a colouring
`c : V → C`. In every synchronous round `t`, every vertex `v` replaces its colour by a function of
the round number, its own colour and the **set** of colours of its neighbours:

  `c_{t+1} v = A.step t (c_t v) {c_t u | u ∈ N(v)}`.

Since only the *set* of neighbouring colours is used, these algorithms also run in the SET-LOCAL
(weak LOCAL) model. The round number is global knowledge (synchronous start); round-independent
algorithms are built with `Algorithm.ofStep`.

## Main definitions

* `LocallyIterative.nbrColors G c v` — the set of colours of the neighbours of `v`.
* `LocallyIterative.Algorithm C` — a round function `ℕ → C → Set C → C`.
* `Algorithm.run G A c₀ t` — the colouring after `t` rounds from `c₀`.
* `IsProper G c` — `c` is a proper colouring (adjacent vertices get different colours).
* `Algorithm.seq A T B` — run `A` for `T` rounds, then `B` (with its own round counter).
* `Algorithm.comap A e d` — run `A` on colours of another type through an encoding `e` / decoding
  `d` with `d ∘ e = id`.

## Main results

* `run_succ_apply`, `run_add`: unfolding; `run_seq_of_le`, `run_seq_add`: phases of `seq`.
* `run_comap`: `comap` simulates `A` on encoded colours.
* `isProper_comp_iff`: properness transfers along injective maps.
* `card_nbrColors_le`: a vertex sees at most `deg v` colours.
-/

@[expose] public section

namespace Cslib.LocallyIterative

variable {V C D : Type*} (G : SimpleGraph V)

/-- The set of colours of the neighbours of `v` under the colouring `c`. -/
def nbrColors (c : V → C) (v : V) : Set C := c '' G.neighborSet v

variable {G} in
theorem mem_nbrColors {c : V → C} {v : V} {x : C} :
    x ∈ nbrColors G c v ↔ ∃ u, G.Adj v u ∧ c u = x := Iff.rfl

variable {G} in
theorem mem_nbrColors_of_adj (c : V → C) {v u : V} (h : G.Adj v u) : c u ∈ nbrColors G c v :=
  ⟨u, h, rfl⟩

theorem nbrColors_comp (f : C → D) (c : V → C) (v : V) :
    nbrColors G (f ∘ c) v = f '' nbrColors G c v := by
  simp only [nbrColors, Set.image_image]; rfl

/-- `c` is a proper colouring of `G`: adjacent vertices receive different colours. -/
def IsProper (c : V → C) : Prop := ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v

variable {G} in
theorem isProper_comp_iff {f : C → D} (hf : Function.Injective f) {c : V → C} :
    IsProper G (f ∘ c) ↔ IsProper G c :=
  ⟨fun h _ _ huv e => h huv (by simp [e]), fun h _ _ huv e => h huv (hf e)⟩

variable {G} in
/-- A proper colouring with values in `α` is a Mathlib `G.Coloring α`. -/
def IsProper.toColoring {c : V → C} (h : IsProper G c) : G.Coloring C :=
  SimpleGraph.Coloring.mk c fun huv => h huv

variable {G} in
theorem isProper_iff_exists_coloring {c : V → C} :
    IsProper G c ↔ ∃ χ : G.Coloring C, ⇑χ = c :=
  ⟨fun h => ⟨h.toColoring, rfl⟩, fun ⟨χ, hχ⟩ _ _ huv => hχ ▸ χ.valid huv⟩

/-- A synchronous locally-iterative algorithm with colour type `C`: in round `t` a vertex with
colour `x` whose neighbours have the set of colours `N` gets the new colour `step t x N`. -/
structure Algorithm (C : Type*) where
  /-- The round function. -/
  step : ℕ → C → Set C → C

namespace Algorithm

/-- A round-independent algorithm. -/
def ofStep (f : C → Set C → C) : Algorithm C := ⟨fun _ => f⟩

/-- The colouring after `t` synchronous rounds of `A`, starting from `c₀`. -/
def run (A : Algorithm C) (c₀ : V → C) : ℕ → V → C
  | 0 => c₀
  | t + 1 => fun v => A.step t (run A c₀ t v) (nbrColors G (run A c₀ t) v)

variable {G}

@[simp] theorem run_zero (A : Algorithm C) (c₀ : V → C) : A.run G c₀ 0 = c₀ := rfl

theorem run_succ (A : Algorithm C) (c₀ : V → C) (t : ℕ) :
    A.run G c₀ (t + 1) = fun v => A.step t (A.run G c₀ t v) (nbrColors G (A.run G c₀ t) v) := rfl

theorem run_succ_apply (A : Algorithm C) (c₀ : V → C) (t : ℕ) (v : V) :
    A.run G c₀ (t + 1) v = A.step t (A.run G c₀ t v) (nbrColors G (A.run G c₀ t) v) := rfl

/-- Shift the round counter by `s`. -/
def shift (A : Algorithm C) (s : ℕ) : Algorithm C := ⟨fun t => A.step (s + t)⟩

theorem run_add (A : Algorithm C) (c₀ : V → C) (s t : ℕ) :
    A.run G c₀ (s + t) = (A.shift s).run G (A.run G c₀ s) t := by
  induction t with
  | zero => rfl
  | succ t ih => funext v; rw [← add_assoc, run_succ_apply, run_succ_apply, ih]; rfl

@[simp] theorem shift_ofStep (f : C → Set C → C) (s : ℕ) : (ofStep f).shift s = ofStep f := rfl

/-- Run `A` for the first `T` rounds and then `B` (whose round counter starts at `0`). -/
def seq (A : Algorithm C) (T : ℕ) (B : Algorithm C) : Algorithm C :=
  ⟨fun t => if t < T then A.step t else B.step (t - T)⟩

theorem run_seq_of_le (A B : Algorithm C) {T : ℕ} (c₀ : V → C) {t : ℕ} (ht : t ≤ T) :
    (A.seq T B).run G c₀ t = A.run G c₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext v
    rw [run_succ_apply, run_succ_apply, ih (by omega)]
    simp [seq, show t < T by omega]

theorem shift_seq (A B : Algorithm C) (T : ℕ) : (A.seq T B).shift T = B := by
  cases B; simp [shift, seq]

theorem run_seq_add (A B : Algorithm C) (T : ℕ) (c₀ : V → C) (t : ℕ) :
    (A.seq T B).run G c₀ (T + t) = B.run G (A.run G c₀ T) t := by
  rw [run_add, shift_seq, run_seq_of_le _ _ _ le_rfl]

/-- Simulate `A` (colours `C`) on colours `D` through an encoding `e : C → D` and a decoding
`d : D → C`. -/
def comap (A : Algorithm C) (e : C → D) (d : D → C) : Algorithm D :=
  ⟨fun t x N => e (A.step t (d x) (d '' N))⟩

theorem run_comap (A : Algorithm C) {e : C → D} {d : D → C} (hed : ∀ x, d (e x) = x)
    (c₀ : V → C) (t : ℕ) : (A.comap e d).run G (e ∘ c₀) t = e ∘ A.run G c₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext v
    rw [run_succ_apply, Function.comp_apply, run_succ_apply, ih]
    simp only [comap, Function.comp_apply, hed, nbrColors_comp, Set.image_image, Set.image_id']

/-- Invariants of runs. -/
theorem run_induction (A : Algorithm C) (c₀ : V → C) {P : (V → C) → Prop} (h0 : P c₀)
    (hstep : ∀ t, P (A.run G c₀ t) → P (A.run G c₀ (t + 1))) (t : ℕ) : P (A.run G c₀ t) := by
  induction t with
  | zero => exact h0
  | succ t ih => exact hstep t ih

end Algorithm

section Degree

variable {G} [G.LocallyFinite]

theorem finite_nbrColors (c : V → C) (v : V) : (nbrColors G c v).Finite :=
  (G.neighborSet v).toFinite.image c

/-- A vertex sees at most `deg v` distinct colours. -/
theorem ncard_nbrColors_le (c : V → C) (v : V) : (nbrColors G c v).ncard ≤ G.degree v := by
  rw [nbrColors, ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]
  exact Set.ncard_image_le (G.neighborSet v).toFinite

end Degree

end Cslib.LocallyIterative
