/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.DynamicNetworks.Product
public import Mathlib.Data.ENat.Lattice
public import Cslib.Foundations.Data.Nat.Growth
public import Cslib.Foundations.Combinatorics.Digraph.Walk

/-!
# Journeys (temporal reachability) in dynamic networks

A dynamic network on a vertex type `α` is a sequence `E : ℕ → α → α → Prop` of directed graphs
(`E k y z`: `y` sends to `z` in the round between time `k` and time `k + 1`; same convention as
`Cslib.DynNet` and `Cslib.HeardOf.Graph`). A *journey* from `x` at time `s` to `y` at time `t` is
a sequence of vertices `x = z_s, z_{s+1}, …, z_t = y` in which every step either stays put or
follows an edge of the current round: the causal order "`(x, s) ↝ (y, t)`" of Lamport/Kuhn–Moses–
Oshman, the "heard-of" relation, the journeys of time-varying graphs (Casteigts et al.) and the
message chains of synchronous crash models are all instances.

## Main definitions

* `DynNet.Journey E s x t y`: there is a journey from `(x, s)` to `(y, t)` (inductive, one round
  at a time).
* `DynNet.tdist E s x y : ℕ∞`: the temporal distance — the least `k` such that a journey starting
  at time `s` reaches `y` by time `s + k` (`⊤` if there is none).
* `DynNet.past E V u t s`: the causal past of `(u, t)` at time `s` among the vertices `V`, i.e.
  the vertices `v ∈ V` with a journey from `(v, s)` to `(u, t)`. `V` is a `Finset`, so that the
  vertex set may vary (e.g. the vertices of one execution among natural-number identifiers).

## Main results

* `Journey.trans`, `Journey.cons`, `Journey.front`, `Journey.mono_left`, `Journey.mono_right`:
  concatenation, prepending / splitting off the first step, enlarging the time window.
* `journey_iff_prod`: journeys are the products (`DynNet.prod`) of the reflexive closures of the
  rounds, so `prod`-based statements (e.g. `inNbhd`, `Broadcasts`) can be read as journey
  statements.
* `journey_succ_iff`, `journey_shift_iff`, `tdist_le_iff`, `tdist_eq_zero_iff`,
  `tdist_lt_top_iff`.
* `isRoot_iff`: rooted rounds are rooted digraphs (`Digraph.IsRoot`).
* `Journey.of_inv`: a property of (time, vertex) pairs preserved by every step of a journey holds
  at its end ("speed of information" arguments).
* **Flooding.** If every round is connected towards `u`, the past grows by at least one vertex per
  round until it is all of `V`: `past_ssubset`, `min_card_le_card_past`
  (`|past(u, t)(t - j)| ≥ min(|V|, j + 1)`), `past_eq_of_card_le` (after `|V| - 1` rounds, `u` has
  heard from every vertex). The counting step is `Nat.min_add_le_of_grow`.
-/

@[expose] public section

namespace Cslib.DynNet

open Relation

variable {α : Type*} {E : ℕ → α → α → Prop}

/-- `Journey E s x t y`: there is a journey in the dynamic network `E` from `x` at time `s` to `y`
at time `t`, i.e. vertices `x = z_s, …, z_t = y` with `z_{k+1} = z_k ∨ E k z_k z_{k+1}`. -/
inductive Journey (E : ℕ → α → α → Prop) (s : ℕ) (x : α) : ℕ → α → Prop
  /-- The empty journey. -/
  | refl : Journey E s x s x
  /-- Append one round: stay at `y` or follow an edge of round `t`. -/
  | step {y z : α} {t : ℕ} : Journey E s x t y → (y = z ∨ E t y z) → Journey E s x (t + 1) z

namespace Journey

variable {s t r : ℕ} {x y z : α}

/-- Journeys go forward in time. -/
theorem le (h : Journey E s x t y) : s ≤ t := by
  induction h with
  | refl => exact le_rfl
  | step _ _ ih => omega

/-- Stay at the endpoint for one more round. -/
theorem stay (h : Journey E s x t y) : Journey E s x (t + 1) y :=
  .step h (Or.inl rfl)

/-- A journey along one edge. -/
theorem single (h : E t x y) : Journey E t x (t + 1) y :=
  .step .refl (Or.inr h)

/-- Staying at a vertex is a journey. -/
theorem self (h : s ≤ t) : Journey E s x t x := by
  induction t with
  | zero => obtain rfl : s = 0 := by omega
            exact .refl
  | succ t ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact .refl
    · exact (ih (by omega)).stay

/-- Concatenation of journeys. -/
theorem trans (h₁ : Journey E s x r y) (h₂ : Journey E r y t z) : Journey E s x t z := by
  induction h₂ with
  | refl => exact h₁
  | step _ hs ih => exact .step ih hs

/-- A journey of no rounds is trivial. -/
theorem eq_of_le (h : Journey E s x t y) (hts : t ≤ s) : x = y := by
  cases h with
  | refl => rfl
  | step h _ => exact absurd h.le (by omega)

/-- A journey from time `t` to time `t` is trivial. -/
theorem same_time (h : Journey E t x t y) : x = y := h.eq_of_le le_rfl

/-- Prepend a step. -/
theorem cons (hxy : x = y ∨ E s x y) (h : Journey E (s + 1) y t z) : Journey E s x t z :=
  trans (.step .refl hxy) h

/-- Split off the first step of a journey. -/
theorem front (h : Journey E s x t z) (hst : s < t) :
    ∃ y, (x = y ∨ E s x y) ∧ Journey E (s + 1) y t z := by
  induction h with
  | refl => omega
  | @step w u t hw hwu ih =>
    rcases Nat.eq_or_lt_of_le hw.le with h | h
    · subst h
      obtain rfl := hw.same_time
      exact ⟨u, hwu, .refl⟩
    · obtain ⟨y, hy, hr⟩ := ih h
      exact ⟨y, hy, .step hr hwu⟩

/-- A vertex without outgoing edges reaches only itself. -/
theorem eq_of_no_out (hx : ∀ k y, ¬ E k x y) (h : Journey E s x t z) : x = z := by
  induction h with
  | refl => rfl
  | step _ hyz ih =>
    obtain rfl := ih
    exact hyz.resolve_right (hx _ _)

/-- A vertex without incoming edges is reached only by itself. -/
theorem eq_of_no_in (hz : ∀ k y, ¬ E k y z) (h : Journey E s x t z) : x = z := by
  induction h with
  | refl => rfl
  | step _ hyz ih =>
    obtain rfl := hyz.resolve_right (hz _ _)
    exact ih hz

/-- No journey uses a window `[s, t)` of rounds without edges. -/
theorem eq_of_empty (hE : ∀ k, s ≤ k → k < t → ∀ a b, ¬ E k a b) (h : Journey E s x t z) :
    x = z := by
  induction h with
  | refl => rfl
  | step h hyz ih =>
    obtain rfl := ih fun k h1 h2 => hE k h1 (by omega)
    exact hyz.resolve_right (hE _ h.le (by omega) _ _)

/-- A journey that leaves its source has a first edge. -/
theorem exists_first_edge (h : Journey E s x t z) (hxz : x ≠ z) :
    ∃ k y, s ≤ k ∧ E k x y ∧ Journey E (k + 1) y t z := by
  induction h with
  | refl => exact absurd rfl hxz
  | @step y z t h hyz ih =>
    by_cases hxy : x = y
    · subst hxy
      rcases hyz with rfl | hyz
      · exact absurd rfl hxz
      · exact ⟨t, z, h.le, hyz, .refl⟩
    · obtain ⟨k, w, hk, hw, hj⟩ := ih hxy
      exact ⟨k, w, hk, hw, .step hj hyz⟩

/-- Start earlier (stay at the source in the meantime). -/
theorem mono_left (h : Journey E s x t y) (hss : r ≤ s) : Journey E r x t y :=
  trans (self hss) h

/-- Arrive later (stay at the target in the meantime). -/
theorem mono_right (h : Journey E s x t y) (htt : t ≤ r) : Journey E s x r y :=
  h.trans (self htt)

end Journey

/-- Journeys of no rounds are trivial. -/
theorem journey_self_iff {s : ℕ} {x y : α} : Journey E s x s y ↔ x = y :=
  ⟨Journey.same_time, fun h => h ▸ .refl⟩

/-- Split off the last round of a journey. -/
theorem journey_succ_iff {s t : ℕ} {x z : α} (hst : s ≤ t) :
    Journey E s x (t + 1) z ↔ ∃ y, Journey E s x t y ∧ (y = z ∨ E t y z) := by
  constructor
  · intro h
    cases h with
    | refl => omega
    | step h hs => exact ⟨_, h, hs⟩
  · rintro ⟨y, h, hs⟩
    exact .step h hs

/-- **Journeys are products of reflexive closures** (`Cslib.DynNet.prod`): `prod`-based statements
(e.g. `inNbhd`, `Broadcasts`) can be read as journey statements. -/
theorem journey_iff_prod {s t : ℕ} {x y : α} :
    Journey E s x t y ↔ s ≤ t ∧ prod (fun k => ReflGen (E k)) s (t - s) x y := by
  constructor
  · intro h
    induction h with
    | refl => simp
    | @step y z t h hs ih =>
      refine ⟨by have := h.le; omega, ?_⟩
      rw [show t + 1 - s = (t - s) + 1 by have := h.le; omega, prod_succ_apply]
      refine ⟨y, ih.2, ?_⟩
      rw [show s + (t - s) = t by have := h.le; omega]
      rcases hs with rfl | hs
      · exact ReflGen.refl
      · exact ReflGen.single hs
  · rintro ⟨hst, h⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
    rw [Nat.add_sub_cancel_left] at h
    induction k generalizing y with
    | zero => simpa using (show x = y from h) ▸ Journey.refl
    | succ k ih =>
      obtain ⟨z, hz, hzy⟩ := prod_succ_apply.1 h
      refine .step (ih (Nat.le_add_right _ _) hz) ?_
      rw [← Nat.add_assoc] at *
      cases hzy with
      | refl => exact Or.inl rfl
      | single h => exact Or.inr h

/-- Journeys in a shifted dynamic network. -/
theorem journey_shift_iff {i s t : ℕ} {x y : α} :
    Journey (fun k => E (i + k)) s x t y ↔ Journey E (i + s) x (i + t) y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | step _ hs ih => exact .step ih hs
  · intro h
    generalize ht : i + t = t' at h
    induction h generalizing t with
    | refl => obtain rfl : t = s := by omega
              exact .refl
    | @step y z t'' h hs ih =>
      obtain ⟨t₀, rfl⟩ : ∃ t₀, t = t₀ + 1 := ⟨t - 1, by have := h.le; omega⟩
      exact .step (ih (by omega)) (by rwa [show t'' = i + t₀ by omega] at hs)

/-! ### Temporal distance -/

/-- The temporal distance `d̂_s(x, y)`: the least `k` such that some journey from `x` at time `s`
reaches `y` by time `s + k` (`0` iff `x = y`, `⊤` if there is no journey). -/
noncomputable def tdist (E : ℕ → α → α → Prop) (s : ℕ) (x y : α) : ℕ∞ :=
  sInf ((fun k : ℕ => (k : ℕ∞)) '' {k | Journey E s x (s + k) y})

/-- `d̂_s(x, y) ≤ k` iff `y` is reached from `(x, s)` by time `s + k`. -/
theorem tdist_le_iff {s : ℕ} {x y : α} {k : ℕ} : tdist E s x y ≤ k ↔ Journey E s x (s + k) y := by
  constructor
  · intro h
    have hne : ((fun k : ℕ => (k : ℕ∞)) '' {k | Journey E s x (s + k) y}).Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      simp only [tdist, hc, sInf_empty, top_le_iff, ENat.natCast_ne_top] at h
    obtain ⟨m, hm, hmeq⟩ := csInf_mem hne
    have : (m : ℕ∞) ≤ k := by unfold tdist at h; rw [← hmeq] at h; exact h
    exact hm.mono_right (by have := ENat.natCast_le_natCast.mp this; omega)
  · intro h
    exact sInf_le ⟨k, h, rfl⟩

/-- The temporal distance vanishes only on the diagonal. -/
theorem tdist_eq_zero_iff {s : ℕ} {x y : α} : tdist E s x y = 0 ↔ x = y := by
  rw [← nonpos_iff_eq_zero, show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, tdist_le_iff,
    Nat.add_zero, journey_self_iff]

/-- The temporal distance is finite iff some journey exists. -/
theorem tdist_lt_top_iff {s : ℕ} {x y : α} : tdist E s x y < ⊤ ↔ ∃ t, Journey E s x t y := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h.ne
    exact ⟨_, tdist_le_iff.mp hk.symm.le⟩
  · rintro ⟨t, ht⟩
    have : tdist E s x y ≤ (t - s : ℕ) := tdist_le_iff.mpr (ht.mono_right (by omega))
    exact lt_of_le_of_lt this (ENat.natCast_lt_top _)

/-! ### Rooted rounds -/

/-- `Cslib.DynNet.IsRoot E r` is rootedness in the digraph with arcs `E`. -/
theorem isRoot_iff {E : α → α → Prop} {r : α} : IsRoot E r ↔ (Digraph.mk E).IsRoot r :=
  Iff.rfl

/-! ### Forward invariants -/

/-- **Forward invariant along a journey.** If `P s x` holds and every step of round `τ` (staying
put or following an edge of round `τ`, for `s ≤ τ < t`) preserves `P`, then `P t y` holds at the
end of every journey from `(x, s)` to `(y, t)`. -/
theorem Journey.of_inv {P : ℕ → α → Prop} {s t : ℕ} {x y : α} (h : Journey E s x t y)
    (h0 : P s x) (hstep : ∀ τ a b, s ≤ τ → τ < t → P τ a → (a = b ∨ E τ a b) → P (τ + 1) b) :
    P t y := by
  induction h with
  | refl => exact h0
  | @step w u t hr hwu ih =>
    exact hstep t w u hr.le (by omega) (ih fun τ a b h1 h2 => hstep τ a b h1 (by omega)) hwu

/-! ### The causal past -/

open Classical in
/-- The causal past of `(u, t)` at time `s` among the vertices `V`: the vertices `v ∈ V` with a
journey from `(v, s)` to `(u, t)` (`past_{(u, t)}(s)` of Kuhn–Moses–Oshman). -/
noncomputable def past (E : ℕ → α → α → Prop) (V : Finset α) (u : α) (t s : ℕ) : Finset α :=
  V.filter fun v => Journey E s v t u

variable {V : Finset α} {u v : α} {t s : ℕ}

/-- Membership in the causal past. -/
theorem mem_past : v ∈ past E V u t s ↔ v ∈ V ∧ Journey E s v t u := by
  classical
  simp [past]

/-- The causal past consists of vertices of `V`. -/
theorem past_subset (u : α) (t s : ℕ) : past E V u t s ⊆ V := fun _ hv => (mem_past.1 hv).1

/-- A vertex of `V` is in its own causal past at any earlier time. -/
theorem self_mem_past (hu : u ∈ V) (h : s ≤ t) : u ∈ past E V u t s :=
  mem_past.2 ⟨hu, Journey.self h⟩

/-- The past at a later time `s'` is contained in the past at time `s ≤ s'`. -/
theorem past_anti {s s' : ℕ} (h : s ≤ s') : past E V u t s' ⊆ past E V u t s := fun _ hv =>
  mem_past.2 ⟨(mem_past.1 hv).1, (mem_past.1 hv).2.mono_left h⟩

/-- The past of `(u, t)` grows with `t`. -/
theorem past_mono {t t' : ℕ} (h : t ≤ t') : past E V u t s ⊆ past E V u t' s := fun _ hv =>
  mem_past.2 ⟨(mem_past.1 hv).1, (mem_past.1 hv).2.trans (Journey.self h)⟩

/-- **The past grows across a round.** If the edges of round `s` start in `V` and some vertex
outside the past at time `s + 1` reaches the past at time `s + 1` along edges of round `s`, then
the past at time `s` is strictly larger. -/
theorem past_ssubset_of_reflTransGen (hE : ∀ x y, E s x y → x ∈ V) {y x : α}
    (hy' : y ∉ past E V u t (s + 1)) (hx : x ∈ past E V u t (s + 1))
    (h : ReflTransGen (E s) y x) : past E V u t (s + 1) ⊂ past E V u t s := by
  refine Finset.ssubset_iff_subset_ne.2 ⟨past_anti s.le_succ, fun heq => ?_⟩
  obtain ⟨z, w, hzw, hz, hw⟩ :=
    exists_edge_cross (S := fun x => x ∈ past E V u t (s + 1)) h hy' hx
  exact hz (heq ▸ mem_past.2 ⟨hE _ _ hzw, Journey.cons (Or.inr hzw) (mem_past.1 hw).2⟩)

/-- **The past grows in a connected round.** If the edges of round `s < t` start in `V`, every
vertex of `V` reaches `u ∈ V` along edges of round `s`, and the past at time `s + 1` is not yet
all of `V`, then the past at time `s` is strictly larger. -/
theorem past_ssubset (hE : ∀ x y, E s x y → x ∈ V) (hconn : ∀ y ∈ V, ReflTransGen (E s) y u)
    (hu : u ∈ V) (hst : s < t) (hne : past E V u t (s + 1) ≠ V) :
    past E V u t (s + 1) ⊂ past E V u t s := by
  obtain ⟨y, hy, hy'⟩ : ∃ y ∈ V, y ∉ past E V u t (s + 1) := by
    by_contra! h
    exact hne (Finset.Subset.antisymm (past_subset u t _) h)
  exact past_ssubset_of_reflTransGen hE hy' (self_mem_past hu hst) (hconn y hy)

/-- **Flooding lemma.** If the edges of every round start in `V` and every vertex of `V` reaches
`u ∈ V` in every round before `t`, then `|past(u, t)(t - j)| ≥ min(|V|, j + 1)` for `j ≤ t`. -/
theorem min_card_le_card_past (hE : ∀ r x y, E r x y → x ∈ V)
    (hconn : ∀ r < t, ∀ y ∈ V, ReflTransGen (E r) y u) (hu : u ∈ V) {j : ℕ} (hj : j ≤ t) :
    min V.card (j + 1) ≤ (past E V u t (t - j)).card := by
  have h0 : 1 ≤ (past E V u t (t - 0)).card := Finset.card_pos.2 ⟨u, self_mem_past hu (by omega)⟩
  have := Nat.min_add_le_of_grow (f := fun i => (past E V u t (t - i)).card) (n := V.card) (K := j)
    (fun i hi => Finset.card_le_card (past_anti (by omega)))
    (fun i hi hlt => by
      have e : t - i = t - (i + 1) + 1 := by omega
      simp only [e] at hlt ⊢
      refine Finset.card_lt_card (past_ssubset (hE _) (hconn _ (by omega)) hu (by omega) ?_)
      rintro h; rw [h] at hlt; exact lt_irrefl _ hlt)
  omega

/-- **Flooding.** Under the hypotheses of `min_card_le_card_past`, the past of `(u, t)` at any
time `s` with `s + |V| ≤ t + 1` is all of `V`. -/
theorem past_eq_of_card_le (hE : ∀ r x y, E r x y → x ∈ V)
    (hconn : ∀ r < t, ∀ y ∈ V, ReflTransGen (E r) y u) (hu : u ∈ V) (h : s + V.card ≤ t + 1) :
    past E V u t s = V := by
  have hn : 0 < V.card := Finset.card_pos.2 ⟨u, hu⟩
  have := min_card_le_card_past hE hconn hu (j := t - s) (by omega)
  rw [show t - (t - s) = s by omega] at this
  exact Finset.eq_of_subset_of_card_le (past_subset _ _ _) (by omega)

end Cslib.DynNet
