/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Foundations.Combinatorics.SimpleGraph.Ball
public import Cslib.Computability.Distributed.Local.LocallyIterative

/-!
# Locality: what a node learns in `R` rounds of the LOCAL model

In the LOCAL model with unique identifiers, the nodes of every graph are the elements of a fixed
type `V` (the identifiers), so two graphs `G G' : SimpleGraph V` and node labellings
`x x' : V → α` (inputs, certificates, states) can be compared directly. In `R` synchronous rounds a
node `v` learns exactly the edges incident to nodes at distance `< R` from `v` and the labels of the
nodes at distance `≤ R`. This file makes that extensional notion of locality precise and connects
it to the locally-iterative model (the bridge to the Online-LOCAL model is in
`Cslib.Computability.Distributed.Local.OnlineLocalLocality`).

## Main definitions

* `GAgree G G' v R`: `G` and `G'` have the same edges at all nodes at distance `< R` from `v`
  (no condition on edges between two nodes at distance exactly `R`).
* `ViewEq R G x G' x' v`: `GAgree G G' v R` and `x`, `x'` agree on the nodes at distance `≤ R`.
* `IsLocal R f`: `f G x v` only depends on the radius-`R` view of `v`, i.e. `f` is computed by an
  `R`-round LOCAL algorithm.
* `loc G v R`, `mask G v R x`: the part of a configuration seen from `v` within radius `R`
  (the *localization trick*: a function of `loc`/`mask` is local by construction).

## Main results

* `GAgree.symm`, `GAgree.trans`, `GAgree.edist_eq`, `GAgree.edist_le_iff`: distances up to `R`
  are the same in both graphs; `GAgree.mono`: agreement around `v` gives agreement around nearby
  nodes with a smaller radius.
* `IsLocal.mono`, `IsLocal.comp`: radii add up under composition.
* `IsLocal.apply_loc`: a `ρ`-local function can be evaluated on the localized configuration.
* `Cslib.LocallyIterative.Algorithm.run_isLocal`: the state of a locally-iterative algorithm after
  `t` rounds is a `t`-local function of the initial states.
-/

@[expose] public section

namespace Cslib.Local

open SimpleGraph

variable {V α β γ : Type*} {G G' G'' : SimpleGraph V} {u v x : V} {R : ℕ}

/-! ### Agreement of graphs around a node -/

/-- `G` and `G'` agree on everything a node `u` can learn about the graph in `R` rounds of the
LOCAL model: the edges incident to nodes at distance `< R` from `u`. (Node names, i.e.
identifiers, are the same in both graphs since they share the vertex type.) -/
def GAgree (G G' : SimpleGraph V) (u : V) (R : ℕ) : Prop :=
  ∀ ⦃x⦄, G.edist u x < R → ∀ y, (G.Adj x y ↔ G'.Adj x y)

namespace GAgree

/-- Every graph agrees with itself. -/
lemma refl (G : SimpleGraph V) (u : V) (R : ℕ) : GAgree G G u R := fun _ _ _ => Iff.rfl

/-- Every graph agrees with itself (implicit version). -/
lemma rfl : GAgree G G u R := refl G u R

/-- Transport of distances along a one-sided agreement: if every edge leaving a node `y` with
`d_G(u, y) = m < R` and `d_{G'}(u, y) ≤ m` is also an edge of `G'`, then `d_G(u, x) = m ≤ R`
implies `d_{G'}(u, x) ≤ m`. -/
private lemma edist_le_of_eq_aux
    (hadj : ∀ ⦃y⦄ (m : ℕ), m < R → G.edist u y = m → G'.edist u y ≤ m →
      ∀ x, G.Adj y x → G'.Adj y x) :
    ∀ (m : ℕ) {x}, G.edist u x = m → m ≤ R → G'.edist u x ≤ m := by
  intro m
  induction m with
  | zero =>
    intro x hx _
    simp only [Nat.cast_zero, edist_eq_zero_iff] at hx
    subst hx; simp
  | succ m ih =>
    intro x hx hm
    obtain ⟨y, hy, hyx⟩ := exists_adj_of_edist_eq_succ hx
    have h1 := ih hy (by omega)
    have h2 : G'.Adj y x := hadj m (by omega) hy h1 x hyx
    calc G'.edist u x ≤ G'.edist u y + 1 := edist_le_add_one_of_adj h2
      _ ≤ m + 1 := by gcongr
      _ = ((m + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-- Distances up to `R` from `u` in `G` bound those in `G'`. -/
private lemma edist_le_of_eq (hA : GAgree G G' u R) :
    ∀ (m : ℕ) {x}, G.edist u x = m → m ≤ R → G'.edist u x ≤ m :=
  edist_le_of_eq_aux fun _ m hm hy _ x => (hA (by rw [hy]; exact_mod_cast hm) x).1

/-- Agreement is symmetric. -/
lemma symm (hA : GAgree G G' u R) : GAgree G' G u R := by
  -- first: `G'.edist u x = m ≤ R` implies `G.edist u x ≤ m`
  have key : ∀ (m : ℕ) {x}, G'.edist u x = m → m ≤ R → G.edist u x ≤ m :=
    edist_le_of_eq_aux fun _ m hm _ h1 x =>
      (hA (lt_of_le_of_lt h1 (by exact_mod_cast hm)) x).2
  intro x hx y
  have hne : G'.edist u x ≠ ⊤ := ne_top_of_lt hx
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
  have hmR : m < R := by rw [← hm] at hx; exact_mod_cast hx
  have := key m hm.symm hmR.le
  exact (hA (lt_of_le_of_lt this (by exact_mod_cast hmR)) y).symm

/-- Agreement is symmetric (as an equivalence). -/
lemma comm : GAgree G G' u R ↔ GAgree G' G u R := ⟨symm, symm⟩

/-- Distances up to `R` from `u` are the same in both graphs. -/
lemma edist_le_iff (hA : GAgree G G' u R) {m : ℕ} (hm : m ≤ R) :
    G'.edist u x ≤ m ↔ G.edist u x ≤ m := by
  have aux : ∀ {G G' : SimpleGraph V}, GAgree G G' u R → G.edist u x ≤ m → G'.edist u x ≤ m := by
    intro G G' hA h
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (edist_ne_top_of_le_natCast h)
    rw [← hj] at h
    have hjm : j ≤ m := by exact_mod_cast h
    exact (hA.edist_le_of_eq j hj.symm (hjm.trans hm)).trans (by exact_mod_cast hjm)
  exact ⟨aux hA.symm, aux hA⟩

/-- Distances up to `R` from `u` are equal in both graphs. -/
lemma edist_eq (hA : GAgree G G' u R) (hx : G.edist u x ≤ R) :
    G'.edist u x = G.edist u x := by
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (edist_ne_top_of_le_natCast hx)
  have hjR : j ≤ R := by rw [← hj] at hx; exact_mod_cast hx
  apply le_antisymm
  · rw [← hj]; exact (hA.edist_le_iff hjR).2 hj.symm.le
  · have h' : G'.edist u x ≤ j := (hA.edist_le_iff hjR).2 hj.symm.le
    obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.1 (edist_ne_top_of_le_natCast h')
    have hij : i ≤ j := by rw [← hi] at h'; exact_mod_cast h'
    have := (hA.edist_le_iff (m := i) (hij.trans hjR)).1 hi.symm.le
    rw [← hi]; exact this

/-- Distances up to `R` from `u` are equal in both graphs (`dist` version). -/
lemma dist_eq (hA : GAgree G G' u R) (hx : G.edist u x ≤ R) : G'.dist u x = G.dist u x := by
  simp only [SimpleGraph.dist, hA.edist_eq hx]

/-- Strict distance bounds up to `R` from `u` are the same in both graphs. -/
lemma edist_lt_iff (hA : GAgree G G' u R) {m : ℕ} (hm : m ≤ R) :
    G'.edist u x < m ↔ G.edist u x < m := by
  cases m with
  | zero => simp
  | succ m =>
    have h1 : ∀ {e : ℕ∞}, e < ((m + 1 : ℕ) : ℕ∞) ↔ e ≤ m := by
      intro e; rw [Nat.cast_add, Nat.cast_one]; exact ENat.lt_add_one_iff (ENat.natCast_ne_top m)
    rw [h1, h1]; exact hA.edist_le_iff (by omega)

/-- Closed balls of radius `≤ R` around `u` are the same in both graphs. -/
lemma closedBall_eq (hA : GAgree G G' u R) {m : ℕ} (hm : m ≤ R) :
    G'.closedBall u m = G.closedBall u m := by
  ext x; simp only [mem_closedBall']; exact hA.edist_le_iff hm

/-- Agreement is transitive. -/
lemma trans (h₁ : GAgree G G' u R) (h₂ : GAgree G' G'' u R) : GAgree G G'' u R :=
  fun _ hx y => (h₁ hx y).trans (h₂ ((h₁.edist_lt_iff le_rfl).2 hx) y)

/-- Agreement around `u` with radius `R` gives agreement around any `x` with `d(u, x) ≤ a` with
radius `ρ`, as long as `a + ρ ≤ R`. -/
lemma mono (hA : GAgree G G' u R) {a ρ : ℕ} (hx : G.edist u x ≤ a) (h : a + ρ ≤ R) :
    GAgree G G' x ρ := by
  intro y hy z
  apply hA
  calc G.edist u y ≤ G.edist u x + G.edist x y := G.edist_triangle
    _ < a + ρ := by
      obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (edist_ne_top_of_le_natCast hx)
      rw [← hj] at hx ⊢
      have hy' : G.edist x y ≠ ⊤ := ne_top_of_lt hy
      obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.1 hy'
      rw [← hi] at hy ⊢
      have : j ≤ a := by exact_mod_cast hx
      have : i < ρ := by exact_mod_cast hy
      exact_mod_cast (by omega : j + i < a + ρ)
    _ ≤ R := by exact_mod_cast h

/-- Agreement with radius `R` gives agreement with any smaller radius. -/
lemma mono_radius (hA : GAgree G G' u R) {ρ : ℕ} (h : ρ ≤ R) : GAgree G G' u ρ :=
  hA.mono (a := 0) (by simp) (by omega)

/-- For a positive radius, the neighbours of `u` are the same in both graphs. -/
lemma adj_iff (hA : GAgree G G' u R) (hR : 0 < R) (y : V) : G.Adj u y ↔ G'.Adj u y :=
  hA (by simp only [edist_self, Nat.cast_pos']; exact hR) y

/-- For a positive radius, the neighbour sets of `u` are the same in both graphs. -/
lemma neighborSet_eq (hA : GAgree G G' u R) (hR : 0 < R) :
    G.neighborSet u = G'.neighborSet u := by
  ext y; exact hA.adj_iff hR y

end GAgree

/-! ### Views and local functions -/

/-- `v` sees the same labelled configuration within radius `R` in `(G, x)` and `(G', x')`: the
edges incident to nodes at distance `< R` agree, and the labels agree on all nodes at distance
`≤ R` (the information gathered in `R` rounds of the LOCAL model). -/
def ViewEq (R : ℕ) (G : SimpleGraph V) (x : V → α) (G' : SimpleGraph V) (x' : V → α) (v : V) :
    Prop :=
  GAgree G G' v R ∧ ∀ u, G.edist v u ≤ R → x u = x' u

/-- `f G x v` only depends on the radius-`R` view of `v`: `f` is computed by an `R`-round LOCAL
algorithm (every node gathers its radius-`R` view and applies a rule). -/
def IsLocal (R : ℕ) (f : SimpleGraph V → (V → α) → V → β) : Prop :=
  ∀ G x G' x' v, ViewEq R G x G' x' v → f G x v = f G' x' v

namespace ViewEq

variable {x₁ x₂ x₃ : V → α}

/-- Every configuration has the same view as itself. -/
lemma refl (R : ℕ) (G : SimpleGraph V) (x : V → α) (v : V) : ViewEq R G x G x v :=
  ⟨.rfl, fun _ _ => Eq.refl _⟩

/-- Changing the labels only outside the radius-`R` ball does not change the view. -/
lemma of_eqOn (h : ∀ u, G.edist v u ≤ R → x₁ u = x₂ u) : ViewEq R G x₁ G x₂ v :=
  ⟨.rfl, h⟩

/-- Equality of views is symmetric. -/
lemma symm (h : ViewEq R G x₁ G' x₂ v) : ViewEq R G' x₂ G x₁ v :=
  ⟨h.1.symm, fun u hu => (h.2 u ((h.1.edist_le_iff le_rfl).1 hu)).symm⟩

/-- Equality of views is transitive. -/
lemma trans (h₁ : ViewEq R G x₁ G' x₂ v) (h₂ : ViewEq R G' x₂ G'' x₃ v) :
    ViewEq R G x₁ G'' x₃ v :=
  ⟨h₁.1.trans h₂.1, fun u hu => (h₁.2 u hu).trans (h₂.2 u ((h₁.1.edist_le_iff le_rfl).2 hu))⟩

/-- Equal views of radius `R` give equal views of any smaller radius. -/
lemma mono {R' : ℕ} (h : ViewEq R G x₁ G' x₂ v) (hR : R' ≤ R) : ViewEq R' G x₁ G' x₂ v :=
  ⟨h.1.mono_radius hR, fun u hu => h.2 u (hu.trans (by exact_mod_cast hR))⟩

end ViewEq

namespace IsLocal

variable {f : SimpleGraph V → (V → α) → V → β}

/-- A `R`-local function is `R'`-local for every `R' ≥ R`. -/
lemma mono {R' : ℕ} (h : IsLocal R f) (hR : R ≤ R') : IsLocal R' f :=
  fun _ _ _ _ _ hv => h _ _ _ _ _ (hv.mono hR)

/-- Running a `ρ`-local algorithm `f` and then a `σ`-local algorithm `g` on its output is a
`(σ + ρ)`-local algorithm. -/
lemma comp {ρ σ : ℕ} {g : SimpleGraph V → (V → β) → V → γ} (hg : IsLocal σ g) (hf : IsLocal ρ f) :
    IsLocal (σ + ρ) (fun G x => g G (f G x)) := by
  intro G x G' x' v hv
  refine hg _ _ _ _ _ ⟨hv.1.mono_radius (by omega), fun u hu => hf _ _ _ _ _ ⟨?_, fun w hw => ?_⟩⟩
  · exact hv.1.mono hu le_rfl
  · exact hv.2 w (by simpa using edist_le_natCast_add hu hw)

end IsLocal

/-- The identity (every node outputs its own label) is `0`-local. -/
lemma isLocal_zero_label : IsLocal (V := V) (α := α) 0 (fun _ x v => x v) :=
  fun _ _ _ _ v hv => hv.2 v (by simp)

/-! ### The localization trick -/

/-- The part of `G` seen from `v` within radius `R`: the edges incident to nodes at distance
`< R` from `v`. -/
def loc (G : SimpleGraph V) (v : V) (R : ℕ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (G.edist v x < R ∨ G.edist v y < R)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

/-- The localized graph is a subgraph. -/
lemma loc_le (G : SimpleGraph V) (v : V) (R : ℕ) : loc G v R ≤ G := fun _ _ h => h.1

/-- A graph and its localization agree around the center. -/
lemma gAgree_loc (G : SimpleGraph V) (v : V) (R : ℕ) : GAgree G (loc G v R) v R :=
  fun _ hx _ => ⟨fun h => ⟨h, Or.inl hx⟩, fun h => h.1⟩

/-- Distances in the localized graph are at least the distances in the graph. -/
lemma edist_le_edist_loc {x y : V} : G.edist x y ≤ (loc G v R).edist x y :=
  edist_anti (loc_le G v R)

/-- Graphs agreeing around `v` have the same localization. -/
lemma loc_eq_of_gAgree (h : GAgree G G' v R) : loc G v R = loc G' v R := by
  ext x y
  simp only [loc]
  constructor
  · rintro ⟨hxy, hx | hy⟩
    · exact ⟨(h hx y).1 hxy, Or.inl ((h.edist_lt_iff le_rfl).2 hx)⟩
    · exact ⟨((h hy x).1 hxy.symm).symm, Or.inr ((h.edist_lt_iff le_rfl).2 hy)⟩
  · rintro ⟨hxy, hx | hy⟩
    · have hx' := (h.edist_lt_iff le_rfl).1 hx
      exact ⟨(h hx' y).2 hxy, Or.inl hx'⟩
    · have hy' := (h.edist_lt_iff le_rfl).1 hy
      exact ⟨((h hy' x).2 hxy.symm).symm, Or.inr hy'⟩

/-- Distances up to `ρ` from a node `u` with `d(v, u) + ρ ≤ R` are the same in `loc G v R`. -/
lemma loc_edist_le_iff {ρ a : ℕ} {w : V} (hu : G.edist v u ≤ a) (h : a + ρ ≤ R) {m : ℕ}
    (hm : m ≤ ρ) : (loc G v R).edist u w ≤ m ↔ G.edist u w ≤ m :=
  ((gAgree_loc G v R).mono hu h).edist_le_iff hm

/-- Adjacency at nodes `u` with `d(v, u) + 1 ≤ R` is unchanged by localization. -/
lemma loc_adj_iff {a : ℕ} {w : V} (hu : G.edist v u ≤ a) (h : a + 1 ≤ R) :
    (loc G v R).Adj u w ↔ G.Adj u w :=
  (((gAgree_loc G v R).mono hu h) (by simp) w).symm

/-- Restrict a labelling to the radius-`R` ball around `v` (outside, it takes the value at `v`). -/
noncomputable def mask (G : SimpleGraph V) (v : V) (R : ℕ) (x : V → α) : V → α :=
  open scoped Classical in fun u => if G.edist v u ≤ R then x u else x v

/-- Masking keeps the labels within distance `R`. -/
lemma mask_of_le {x : V → α} (h : G.edist v u ≤ R) : mask G v R x u = x u := by
  classical
  simp [mask, h]

/-- Masking commutes with post-composition. -/
lemma mask_comp (f : α → β) (x : V → α) : mask G v R (f ∘ x) = f ∘ mask G v R x := by
  classical
  funext u; simp only [mask, Function.comp_apply]; split_ifs <;> rfl

namespace ViewEq

variable {x₁ x₂ : V → α}

/-- Equal views have equal localized graphs. -/
lemma loc_eq (h : ViewEq R G x₁ G' x₂ v) : loc G v R = loc G' v R :=
  loc_eq_of_gAgree h.1

/-- Equal views have equal masked labellings. -/
lemma mask_eq (h : ViewEq R G x₁ G' x₂ v) : mask G v R x₁ = mask G' v R x₂ := by
  classical
  have hv : G.edist v v ≤ R := by simp
  funext u
  simp only [mask]
  by_cases hu : G.edist v u ≤ R
  · rw [ite_eq_left hu, ite_eq_left ((h.1.edist_le_iff le_rfl).2 hu)]; exact h.2 u hu
  · rw [ite_eq_right hu, ite_eq_right (fun h' => hu ((h.1.edist_le_iff le_rfl).1 h'))]
    exact h.2 v hv

end ViewEq

/-- The view of a node `u` near `v` (`d(v, u) + ρ ≤ R`) in the localized configuration
`(loc G v R, x')` equals its view in `(G, x)`, for any labelling `x'` that agrees with `x` within
distance `R` of `v`. -/
lemma viewEq_loc {ρ a : ℕ} {x x' : V → α} (hu : G.edist v u ≤ a) (h : a + ρ ≤ R)
    (hx : ∀ w, G.edist v w ≤ R → x' w = x w) : ViewEq ρ (loc G v R) x' G x u := by
  have hA : GAgree G (loc G v R) u ρ := (gAgree_loc G v R).mono hu h
  refine ⟨hA.symm, fun w hw => hx w ?_⟩
  have hw' : G.edist u w ≤ ρ := edist_le_edist_loc.trans hw
  simpa using edist_le_natCast_add (hu.trans le_rfl) hw' |>.trans (by exact_mod_cast h)

/-- A `ρ`-local function can be evaluated on the localized configuration `(loc G v R, x')` at any
node `u` with `d(v, u) + ρ ≤ R`. -/
lemma IsLocal.apply_loc {ρ a : ℕ} {f : SimpleGraph V → (V → α) → V → β} (hf : IsLocal ρ f)
    {x x' : V → α} (hu : G.edist v u ≤ a) (h : a + ρ ≤ R)
    (hx : ∀ w, G.edist v w ≤ R → x' w = x w) : f (loc G v R) x' u = f G x u :=
  hf _ _ _ _ _ (viewEq_loc hu h hx)

end Cslib.Local

namespace Cslib.LocallyIterative.Algorithm

open SimpleGraph Cslib.Local

variable {V C : Type*}

/-- One round of a locally-iterative algorithm is `1`-local. -/
lemma isLocal_step (A : Algorithm C) (t : ℕ) :
    IsLocal 1 (fun G (c : V → C) v => A.step t (c v) (nbrColors G c v)) := by
  intro G c G' c' v hv
  have hN := hv.1.neighborSet_eq one_pos
  have hc : ∀ w ∈ G.neighborSet v, c w = c' w := fun w hw =>
    hv.2 w (by rw [edist_eq_one_iff_adj.2 hw]; simp)
  simp only [nbrColors, ← hN, Set.image_congr hc, hv.2 v (by simp)]

/-- The state of a node after `t` rounds of a locally-iterative algorithm only depends on its
radius-`t` view of the graph and of the initial states. -/
theorem run_isLocal (A : Algorithm C) (t : ℕ) :
    IsLocal t (fun G (c₀ : V → C) v => A.run G c₀ t v) := by
  induction t with
  | zero => exact isLocal_zero_label
  | succ t ih =>
    have h := (isLocal_step A t).comp ih
    rwa [Nat.add_comm] at h

end Cslib.LocallyIterative.Algorithm
