/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.ColourSystem.Basic

/-!
# Edge-coloured graphs and their views (universal covers)

A `ColouredGraph k α` is a graph on `α` with edges coloured by `Fin k` such that each node has at
most one incident edge of each colour: `step a c` is the `c`-neighbour of `a`, and `step` is
symmetric. Half-loops (`step a c = some a`) are allowed: in the view they unfold into ordinary
edges (this is how the colour pickers / "self-loops" of Remark 1 of [HirvonenSuomela2012] work).

The **view** of a node `a` (`G.view a ⊆ G_k`) is the set of colour sequences that can be followed
from `a`: the universal covering tree of `G` rooted at `a`, as a colour system. It is exactly what
a deterministic anonymous node can learn in the edge-coloured (port-numbering) model: after `r`
rounds, a node knows `ball (G.view a) (r + 1)`.

Main results:
* `walk_mul`: `walk` is a partial right action of `G_k` (`walk a (x * y) = walk (walk a x) y`).
* `isColourSystem_view`, `view_inv_smul` (`x̄ · view a = view (walk a x)`), `colours_view`.
* `view_map`: covering maps preserve views; `walk_eq_of_agree`: locality of views.
* `tGraph T L`: the graph of a set `T ⊆ G_k` (tree edges) plus half-loops `L s`;
  `view_tGraph_empty`: for a colour system `V` and `a ∈ V`, the view of `a` in `Γ_k(V)` is `ā V`.

## References

* [J. Hirvonen, J. Suomela, *Distributed maximal matching: greedy is optimal*][HirvonenSuomela2012]
-/

@[expose] public section

namespace Cslib.ColourSystem

open FreeCox Pointwise

variable {k : ℕ}

/-- A `k`-edge-coloured graph (each colour class is a partial involution; half-loops allowed). -/
structure ColouredGraph (k : ℕ) (α : Type*) where
  /-- The `c`-neighbour of `a`, if any. -/
  step : α → Fin k → Option α
  symm : ∀ a b c, step a c = some b → step b c = some a

namespace ColouredGraph

variable {α β : Type*} (G : ColouredGraph k α)

/-- Follow a (reversed) list of colours. -/
def walkList (a : α) (l : List (Fin k)) : Option α :=
  l.foldr (fun c o => o.bind (G.step · c)) (some a)

/-- Follow the reduced word of `x` from `a`. -/
def walk (a : α) (x : FreeCox k) : Option α := G.walkList a x.1

/-- The view of `a`: all reduced colour sequences that can be followed from `a` (the universal
cover of `G` rooted at `a`). -/
def view (a : α) : Set (FreeCox k) := {x | (G.walk a x).isSome}

@[simp] theorem walkList_nil (a : α) : G.walkList a [] = some a := rfl

@[simp] theorem walkList_cons (a : α) (c : Fin k) (l : List (Fin k)) :
    G.walkList a (c :: l) = (G.walkList a l).bind (G.step · c) := rfl

theorem walkList_append (a : α) (l m : List (Fin k)) :
    G.walkList a (l ++ m) = (G.walkList a m).bind (G.walkList · l) := by
  induction l with
  | nil => simp [walkList]
  | cons c l ih =>
    rw [List.cons_append, walkList_cons, ih]
    cases G.walkList a m <;> simp

theorem walkList_mulGenList {a e e' : α} {W : List (Fin k)} {c : Fin k}
    (h1 : G.walkList a W = some e') (h2 : G.step e' c = some e) :
    G.walkList a (mulGenList W c) = some e := by
  cases W with
  | nil => simp only [walkList_nil, Option.some.injEq] at h1; subst h1; simpa [mulGenList] using h2
  | cons b W =>
    simp only [mulGenList]
    split_ifs with hb
    · subst hb
      rw [walkList_cons] at h1
      obtain ⟨f, hf, hfe⟩ := Option.bind_eq_some_iff.1 h1
      have := G.symm _ _ _ hfe
      rw [this] at h2
      cases h2
      exact hf
    · rw [walkList_cons, h1]; exact h2

theorem walkList_act {a b e : α} {X Y : List (Fin k)} (h1 : G.walkList a X = some b)
    (h2 : G.walkList b Y = some e) : G.walkList a (act X Y) = some e := by
  induction Y generalizing e with
  | nil => simp only [walkList_nil, Option.some.injEq] at h2; subst h2; exact h1
  | cons c Y ih =>
    rw [walkList_cons] at h2
    obtain ⟨f, hf, hfe⟩ := Option.bind_eq_some_iff.1 h2
    rw [act_cons]
    exact G.walkList_mulGenList (ih hf) hfe

theorem walkList_reverse {a b : α} {X : List (Fin k)} (h : G.walkList a X = some b) :
    G.walkList b X.reverse = some a := by
  induction X generalizing b with
  | nil => simp only [walkList_nil, Option.some.injEq] at h; subst h; rfl
  | cons c X ih =>
    rw [walkList_cons] at h
    obtain ⟨f, hf, hfb⟩ := Option.bind_eq_some_iff.1 h
    rw [List.reverse_cons, walkList_append, walkList_cons, walkList_nil]
    simp only [Option.bind_some, G.symm _ _ _ hfb]
    exact ih hf

@[simp] theorem walk_one (a : α) : G.walk a 1 = some a := rfl

@[simp] theorem walk_gen (a : α) (c : Fin k) : G.walk a (gen c) = G.step a c := by
  simp [walk, walkList]

theorem walk_mul_of_some {a b e : α} {x y : FreeCox k} (h1 : G.walk a x = some b)
    (h2 : G.walk b y = some e) : G.walk a (x * y) = some e :=
  G.walkList_act h1 h2

theorem walk_inv {a b : α} {x : FreeCox k} (h : G.walk a x = some b) : G.walk b x⁻¹ = some a :=
  G.walkList_reverse h

/-- `walk` is a partial right action of `G_k`. -/
theorem walk_mul {a b : α} {x : FreeCox k} (h : G.walk a x = some b) (y : FreeCox k) :
    G.walk a (x * y) = G.walk b y := by
  cases hy : G.walk b y with
  | some e => exact G.walk_mul_of_some h hy
  | none =>
    cases hxy : G.walk a (x * y) with
    | none => rfl
    | some e =>
      have := G.walk_mul_of_some (G.walk_inv h) hxy
      rw [inv_mul_cancel_left, hy] at this
      cases this

theorem walk_mul_gen {a b : α} {x : FreeCox k} (h : G.walk a x = some b) (c : Fin k) :
    G.walk a (x * gen c) = G.step b c := by
  rw [G.walk_mul h, walk_gen]

theorem walk_mul_gen_of_lt (a : α) {x : FreeCox k} {c : Fin k} (h : len x < len (x * gen c)) :
    G.walk a (x * gen c) = (G.walk a x).bind (G.step · c) := by
  have hne : x.1.head? ≠ some c := by
    intro h'; have := (len_mul_gen_lt_iff x c).2 h'; omega
  simp only [walk, mul_gen_val, mulGenList_of_head_ne hne, walkList_cons]

theorem walk_of_mul_gen {a b : α} {x : FreeCox k} {c : Fin k} (h : len x < len (x * gen c))
    (hb : G.walk a (x * gen c) = some b) : ∃ b', G.walk a x = some b' ∧ G.step b' c = some b := by
  rw [G.walk_mul_gen_of_lt a h] at hb
  exact Option.bind_eq_some_iff.1 hb

theorem mem_view {a : α} {x : FreeCox k} : x ∈ G.view a ↔ ∃ b, G.walk a x = some b := by
  simp [view, Option.isSome_iff_exists]

theorem one_mem_view (a : α) : (1 : FreeCox k) ∈ G.view a := by simp [mem_view]

/-- Views are colour systems. -/
theorem isColourSystem_view (a : α) : IsColourSystem (G.view a) := by
  refine ⟨G.one_mem_view a, fun x hx c hc => ?_⟩
  rw [mem_view] at hx ⊢
  obtain ⟨b, hb⟩ := hx
  have h' : len (x * gen c) < len (x * gen c * gen c) := by rw [mul_gen_mul_gen]; exact hc
  rw [← mul_gen_mul_gen x c] at hb
  obtain ⟨b', hb', -⟩ := G.walk_of_mul_gen h' hb
  exact ⟨b', hb'⟩

/-- Lemma 8 of [HirvonenSuomela2012] in general form: the view from `x` only depends on where `x`
leads. -/
theorem view_inv_smul {a b : α} {x : FreeCox k} (h : G.walk a x = some b) :
    x⁻¹ • G.view a = G.view b := by
  ext y
  rw [mem_inv_smul]
  simp only [view, Set.mem_ofPred_eq, G.walk_mul h]

theorem colours_view {a b : α} {x : FreeCox k} (h : G.walk a x = some b) (c : Fin k) :
    c ∈ colours (G.view a) x ↔ (G.step b c).isSome := by
  rw [mem_colours]
  simp only [view, Set.mem_ofPred_eq, G.walk_mul_gen h]

/-! ### Covering maps and locality -/

/-- A covering map (local isomorphism) of coloured graphs commutes with walks. -/
theorem walkList_map (H : ColouredGraph k β) (f : α → β)
    (hf : ∀ a c, H.step (f a) c = (G.step a c).map f) (a : α) (l : List (Fin k)) :
    H.walkList (f a) l = (G.walkList a l).map f := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [walkList_cons, walkList_cons, ih]
    cases G.walkList a l <;> simp [hf]

theorem walk_map (H : ColouredGraph k β) (f : α → β)
    (hf : ∀ a c, H.step (f a) c = (G.step a c).map f) (a : α) (x : FreeCox k) :
    H.walk (f a) x = (G.walk a x).map f :=
  G.walkList_map H f hf a x.1

/-- Covering maps preserve views. -/
theorem view_map (H : ColouredGraph k β) (f : α → β)
    (hf : ∀ a c, H.step (f a) c = (G.step a c).map f) (a : α) : H.view (f a) = G.view a := by
  ext x
  simp [view, G.walk_map H f hf]

/-- A map that is a local isomorphism at all nodes reachable from `a` commutes with walks
from `a`. -/
theorem walk_map_of_reachable (H : ColouredGraph k β) (f : α → β) (a : α)
    (hf : ∀ x b, G.walk a x = some b → ∀ c, H.step (f b) c = (G.step b c).map f)
    (x : FreeCox k) : H.walk (f a) x = (G.walk a x).map f := by
  induction x using FreeCox.induction_on with
  | h1 => rfl
  | hstep x c hxc ih =>
    rw [G.walk_mul_gen_of_lt a hxc, H.walk_mul_gen_of_lt (f a) hxc, ih]
    cases hb : G.walk a x with
    | none => rfl
    | some b => simp [hf x b hb c]

theorem view_map_of_reachable (H : ColouredGraph k β) (f : α → β) (a : α)
    (hf : ∀ x b, G.walk a x = some b → ∀ c, H.step (f b) c = (G.step b c).map f) :
    H.view (f a) = G.view a := by
  ext x
  simp [view, G.walk_map_of_reachable H f a hf]

/-- Bounded version of `walk_map_of_reachable`: a local isomorphism at all nodes reachable from
`a` in fewer than `R` steps preserves walks of length `≤ R`. -/
theorem walk_map_of_reachable_le (H : ColouredGraph k β) (f : α → β) (a : α) (R : ℕ)
    (hf : ∀ x b, len x < R → G.walk a x = some b → ∀ c, H.step (f b) c = (G.step b c).map f)
    (x : FreeCox k) (hx : len x ≤ R) : H.walk (f a) x = (G.walk a x).map f := by
  induction x using FreeCox.induction_on with
  | h1 => rfl
  | hstep x c hxc ih =>
    rw [G.walk_mul_gen_of_lt a hxc, H.walk_mul_gen_of_lt (f a) hxc, ih (by omega)]
    cases hb : G.walk a x with
    | none => rfl
    | some b => simp [hf x b (by omega) hb c]

theorem ball_view_map_le (H : ColouredGraph k β) (f : α → β) (a : α) (R : ℕ)
    (hf : ∀ x b, len x < R → G.walk a x = some b → ∀ c, H.step (f b) c = (G.step b c).map f) :
    ball (H.view (f a)) R = ball (G.view a) R := by
  ext x
  simp only [mem_ball, view, Set.mem_ofPred_eq]
  refine and_congr_left fun hx => ?_
  rw [G.walk_map_of_reachable_le H f a R hf x hx]
  cases G.walk a x <;> simp

/-- Locality: two graphs on the same nodes whose steps agree at all nodes reachable from `a` by
fewer than `R` steps have the same walks of length `≤ R` from `a`. -/
theorem walk_eq_of_agree (H : ColouredGraph k α) (a : α) (R : ℕ)
    (hagree : ∀ x b, len x < R → G.walk a x = some b → ∀ c, G.step b c = H.step b c)
    (x : FreeCox k) (hx : len x ≤ R) : G.walk a x = H.walk a x := by
  induction x using FreeCox.induction_on with
  | h1 => rfl
  | hstep x c hxc ih =>
    rw [G.walk_mul_gen_of_lt a hxc, H.walk_mul_gen_of_lt a hxc, ← ih (by omega)]
    cases hb : G.walk a x with
    | none => rfl
    | some b => simp [hagree x b (by omega) hb c]

theorem ball_view_eq_of_agree (H : ColouredGraph k α) (a : α) (R : ℕ)
    (hagree : ∀ x b, len x < R → G.walk a x = some b → ∀ c, G.step b c = H.step b c) :
    ball (G.view a) R = ball (H.view a) R := by
  ext x
  simp only [mem_ball, view, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, h2⟩
  · rwa [← G.walk_eq_of_agree H a R hagree x h2]
  · rwa [G.walk_eq_of_agree H a R hagree x h2]

end ColouredGraph

/-! ### The graph of a subset of `G_k` with half-loops -/

open Classical in
/-- The coloured graph on `G_k` whose edges are the tree edges of `Γ_k` inside `T`, plus a
half-loop of colour `c` at `s ∈ T` for each `c ∈ L s` with `s c ∉ T`. Nodes outside `T` are
isolated. `tGraph V (fun _ => ∅)` is `Γ_k(V)`. -/
noncomputable def tGraph (T : Set (FreeCox k)) (L : FreeCox k → Set (Fin k)) :
    ColouredGraph k (FreeCox k) where
  step s c :=
    if s ∈ T then (if s * gen c ∈ T then some (s * gen c) else if c ∈ L s then some s else none)
    else none
  symm a b c h := by
    split_ifs at h with ha hac hL <;> cases h
    · simp [ha, hac]
    · simp [ha, hac, hL]

section tGraph

variable {T : Set (FreeCox k)} {L : FreeCox k → Set (Fin k)}

theorem tGraph_step_eq_some {s b : FreeCox k} {c : Fin k} (h : (tGraph T L).step s c = some b) :
    s ∈ T ∧ ((s * gen c ∈ T ∧ b = s * gen c) ∨ (s * gen c ∉ T ∧ c ∈ L s ∧ b = s)) := by
  simp only [tGraph] at h
  split_ifs at h with h1 h2 h3 <;> cases h
  · exact ⟨h1, Or.inl ⟨h2, rfl⟩⟩
  · exact ⟨h1, Or.inr ⟨h2, h3, rfl⟩⟩

theorem tGraph_step_isSome {s : FreeCox k} {c : Fin k} :
    ((tGraph T L).step s c).isSome ↔ s ∈ T ∧ (s * gen c ∈ T ∨ c ∈ L s) := by
  simp only [tGraph]
  split_ifs <;> simp_all

theorem tGraph_step_of_mem {s : FreeCox k} {c : Fin k} (hs : s ∈ T) (hc : s * gen c ∈ T) :
    (tGraph T L).step s c = some (s * gen c) := by
  simp [tGraph, hs, hc]

theorem tGraph_step_of_loop {s : FreeCox k} {c : Fin k} (hs : s ∈ T) (hc : s * gen c ∉ T)
    (hL : c ∈ L s) : (tGraph T L).step s c = some s := by
  simp [tGraph, hs, hc, hL]

theorem tGraph_step_of_not_mem {s : FreeCox k} {c : Fin k} (hs : s ∈ T) (hc : s * gen c ∉ T)
    (hL : c ∉ L s) : (tGraph T L).step s c = none := by
  simp [tGraph, hs, hc, hL]

theorem tGraph_walk_mem {a b : FreeCox k} {x : FreeCox k} (ha : a ∈ T)
    (h : (tGraph T L).walk a x = some b) : b ∈ T := by
  induction x using FreeCox.induction_on generalizing b with
  | h1 => simp only [ColouredGraph.walk_one, Option.some.injEq] at h; rwa [← h]
  | hstep x c hxc ih =>
    obtain ⟨b', hb', hstep⟩ := (tGraph T L).walk_of_mul_gen hxc h
    rcases (tGraph_step_eq_some hstep).2 with ⟨h1, rfl⟩ | ⟨-, -, rfl⟩
    · exact h1
    · exact ih hb'

/-- In `tGraph`, a walk of length `ℓ` ends within distance `ℓ` of its start. -/
theorem tGraph_len_walk_le {a b : FreeCox k} {x : FreeCox k}
    (h : (tGraph T L).walk a x = some b) : len (a⁻¹ * b) ≤ len x := by
  induction x using FreeCox.induction_on generalizing b with
  | h1 => simp only [ColouredGraph.walk_one, Option.some.injEq] at h; subst h; simp
  | hstep x c hxc ih =>
    obtain ⟨b', hb', hstep⟩ := (tGraph T L).walk_of_mul_gen hxc h
    have := ih hb'
    rcases (tGraph_step_eq_some hstep).2 with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · rw [← mul_assoc]
      have := len_mul_gen_le (a⁻¹ * b') c
      omega
    · omega

open Classical in
/-- For a colour system `V` and `a ∈ V`, the view of `a` in `Γ_k(V)` is `ā V`. -/
theorem walk_tGraph_empty {V : Set (FreeCox k)} (hV : IsColourSystem V) {a : FreeCox k}
    (ha : a ∈ V) (x : FreeCox k) :
    (tGraph V fun _ => ∅).walk a x = if a * x ∈ V then some (a * x) else none := by
  induction x using FreeCox.induction_on with
  | h1 => simp [ha]
  | hstep x c hxc ih =>
    rw [(tGraph V fun _ => ∅).walk_mul_gen_of_lt a hxc, ih]
    by_cases hx : a * x ∈ V
    · rw [ite_eq_left hx, Option.bind_some]
      by_cases hxc' : a * x * gen c ∈ V
      · rw [tGraph_step_of_mem hx hxc', ← mul_assoc, ite_eq_left hxc']
      · rw [tGraph_step_of_not_mem hx hxc' (by simp), ← mul_assoc, ite_eq_right hxc']
    · rw [ite_eq_right hx, Option.bind_none, ite_eq_right]
      intro h
      apply hx
      have := hV.mem_of_mul_mem ha h (c := c) (by rw [mul_gen_mul_gen]; exact hxc)
      rwa [mul_gen_mul_gen] at this

theorem view_tGraph_empty {V : Set (FreeCox k)} (hV : IsColourSystem V) {a : FreeCox k}
    (ha : a ∈ V) : (tGraph V fun _ => ∅).view a = a⁻¹ • V := by
  ext x
  rw [mem_inv_smul]
  simp only [ColouredGraph.view, Set.mem_ofPred_eq, walk_tGraph_empty hV ha]
  split_ifs with h <;> simp [h]

theorem tGraph_step_congr {T' : Set (FreeCox k)} {L' : FreeCox k → Set (Fin k)} {b : FreeCox k}
    {c : Fin k} (h1 : b ∈ T ↔ b ∈ T') (h2 : b * gen c ∈ T ↔ b * gen c ∈ T')
    (h3 : c ∈ L b ↔ c ∈ L' b) : (tGraph T L).step b c = (tGraph T' L').step b c := by
  by_cases hb : b ∈ T <;> by_cases hbc : b * gen c ∈ T <;> by_cases hL : c ∈ L b <;>
    simp_all [tGraph]

/-- Translating `T` and `L` by `u` gives an isomorphic graph. -/
theorem tGraph_smul_step (u : FreeCox k) (s : FreeCox k) (c : Fin k) :
    (tGraph (u • T) (fun x => L (u⁻¹ * x))).step (u * s) c =
      ((tGraph T L).step s c).map (u * ·) := by
  have e1 : u * s ∈ u • T ↔ s ∈ T := by rw [mem_smul, inv_mul_cancel_left]
  have e2 : u * (s * gen c) ∈ u • T ↔ s * gen c ∈ T := by
    rw [mem_smul, inv_mul_cancel_left]
  by_cases h1 : s ∈ T <;> by_cases h2 : s * gen c ∈ T <;> by_cases h3 : c ∈ L s <;>
    simp [tGraph, h1, h2, h3, e1, e2, mul_assoc]

theorem view_tGraph_smul (u a : FreeCox k) :
    (tGraph (u • T) (fun x => L (u⁻¹ * x))).view (u * a) = (tGraph T L).view a :=
  (tGraph T L).view_map _ (u * ·) (fun s c => tGraph_smul_step u s c) a

end tGraph

end Cslib.ColourSystem
