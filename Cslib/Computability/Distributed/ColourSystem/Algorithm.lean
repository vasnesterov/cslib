/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.ColourSystem.Graph
public import Mathlib.Algebra.Field.ZMod

/-!
# Deterministic distributed algorithms on colour systems (view-based definition)

Following [HirvonenSuomela2012] (§2.3–2.4): in an anonymous `k`-edge-coloured network a node
initially knows its incident colours, i.e. `(v̄V)[1]`, and after `r` rounds of full-information
message passing it knows precisely `(v̄V)[r+1]`. Accordingly, an algorithm `A` (a map from colour
system and node to a local output) has **running time `r`** if `(ūU)[r+1] = (v̄V)[r+1]` implies
`A U u = A V v`. (The bridge to an explicit round-based message-passing model is in
`Cslib.ColourSystem.MessagePassing`.)

The maximal-matching output convention: `A V v = none` (`⊥`, unmatched) or `some c` (matched
along the edge of colour `c`), subject to (M1)–(M3) (`FindsMaximalMatching`).

## References

* [J. Hirvonen, J. Suomela, *Distributed maximal matching: greedy is optimal*][HirvonenSuomela2012]
-/

@[expose] public section

namespace Cslib.ColourSystem

open FreeCox Pointwise

variable {k : ℕ}

/-- A (deterministic, anonymous) distributed algorithm for edge-coloured trees, given by its
output `A V v ∈ Option (Fin k)` at node `v` of the colour system `V` (only relevant for colour
systems `V` and `v ∈ V`). -/
abbrev Algorithm (k : ℕ) := Set (FreeCox k) → FreeCox k → Option (Fin k)

/-- `A` has running time `r`: the output of `v` only depends on its radius-`(r+1)` view
`(v̄V)[r+1]` (§2.3 of [HirvonenSuomela2012]). -/
def HasRunningTime (A : Algorithm k) (r : ℕ) : Prop :=
  ∀ U V : Set (FreeCox k), ∀ u v : FreeCox k, IsColourSystem U → IsColourSystem V → u ∈ U →
    v ∈ V → ball (u⁻¹ • U) (r + 1) = ball (v⁻¹ • V) (r + 1) → A U u = A V v

/-- `A` finds a maximal matching in the colour system `V` (properties (M1)–(M3), §2.4). -/
def FindsMaximalMatching (A : Algorithm k) (V : Set (FreeCox k)) : Prop :=
  ∀ v ∈ V,
    -- (M1) the output is an incident colour or `⊥`
    (∀ c, A V v = some c → c ∈ colours V v) ∧
    -- (M2) consistency: the partner along colour `c` is matched along `c` too
    (∀ c, A V v = some c → A V (v * gen c) = some c) ∧
    -- (M3) maximality: an unmatched node has only matched neighbours
    (A V v = none → ∀ c ∈ colours V v, A V (v * gen c) ≠ none)

theorem HasRunningTime.mono {A : Algorithm k} {r r' : ℕ} (hA : HasRunningTime A r)
    (h : r ≤ r') : HasRunningTime A r' :=
  fun U V u v hU hV hu hv e => hA U V u v hU hV hu hv (ball_mono (by omega) e)

/-- The output of `v` is the output of the root in the view from `v`. -/
theorem HasRunningTime.apply_eq {A : Algorithm k} {r : ℕ} (hA : HasRunningTime A r)
    {V : Set (FreeCox k)} (hV : IsColourSystem V) {v : FreeCox k} (hv : v ∈ V) :
    A V v = A (v⁻¹ • V) 1 :=
  hA V (v⁻¹ • V) v 1 hV (hV.inv_smul hv) hv (by rw [mem_inv_smul, mul_one]; exact hv)
    (by rw [inv_one, one_smul])

/-- Two colour systems that agree up to radius `r + 1` get the same output at the root. -/
theorem HasRunningTime.apply_one_eq {A : Algorithm k} {r : ℕ} (hA : HasRunningTime A r)
    {U V : Set (FreeCox k)} (hU : IsColourSystem U) (hV : IsColourSystem V)
    (h : ball U (r + 1) = ball V (r + 1)) : A U 1 = A V 1 :=
  hA U V 1 1 hU hV hU.one_mem hV.one_mem (by simpa using h)

/-- A finite set with a fixed-point-free involution has even cardinality. -/
theorem even_card_of_involution {α : Type*} (s : Finset α) (g : α → α) (hg : ∀ a ∈ s, g a ∈ s)
    (hgg : ∀ a ∈ s, g (g a) = a) (hne : ∀ a ∈ s, g a ≠ a) : Even s.card := by
  have := Finset.sum_involution (s := s) (f := fun _ => (1 : ZMod 2)) (fun a _ => g a)
    (fun a _ => by decide) (fun a ha _ => hne a ha) (fun a ha => hg a ha) (fun a ha => hgg a ha)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
  exact (ZMod.natCast_eq_zero_iff_even).1 this

end Cslib.ColourSystem
