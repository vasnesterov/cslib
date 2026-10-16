/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.ColourSystem.FreeCoxeter
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Tactic.Group

/-!
# Colour systems

A `k`-colour system ([HirvonenSuomela2012], §2.2) is a non-empty prefix-closed subset
`V ⊆ G_k`; it is the node set of an edge-coloured subtree `Γ_k(V)` of the Cayley tree `Γ_k`
containing `e`. Every `k`-edge-coloured tree is isomorphic to some `Γ_k(V)`.

* `IsColourSystem V`: `e ∈ V` and the parent of each `v ∈ V - e` is in `V`.
* `ball V h` = `V[h] = {v ∈ V | |v| ≤ h}`.
* `colours V v` = `C(V, v) = {c | vc ∈ V}` (incident colours), `IsRegular V d`.
* `IsPre y x`: `y` lies on the path from `e` to `x`; colour systems are closed under prefixes
  (`IsColourSystem.mem_of_isPre`).
* Re-rooting (Lemma 4 of [HirvonenSuomela2012]): `IsColourSystem.inv_smul` (`ū V` is a colour
  system for `u ∈ V`).

## References

* [J. Hirvonen, J. Suomela, *Distributed maximal matching: greedy is optimal*][HirvonenSuomela2012]
-/

@[expose] public section

namespace Cslib.ColourSystem

open FreeCox Pointwise

variable {k : ℕ}

/-- A `k`-colour system: a non-empty prefix-closed set of elements of `G_k`. -/
def IsColourSystem (V : Set (FreeCox k)) : Prop :=
  (1 : FreeCox k) ∈ V ∧ ∀ x ∈ V, ∀ c, len (x * gen c) < len x → x * gen c ∈ V

/-- `V[h]`: the nodes of `V` within distance `h` of `e`. -/
def ball (V : Set (FreeCox k)) (h : ℕ) : Set (FreeCox k) := {v | v ∈ V ∧ len v ≤ h}

@[simp] theorem mem_ball {V : Set (FreeCox k)} {h : ℕ} {v : FreeCox k} :
    v ∈ ball V h ↔ v ∈ V ∧ len v ≤ h := Iff.rfl

theorem ball_mono {U V : Set (FreeCox k)} {h h' : ℕ} (hh : h' ≤ h) (e : ball U h = ball V h) :
    ball U h' = ball V h' := by
  ext x
  have := Set.ext_iff.1 e x
  simp only [mem_ball] at this ⊢
  constructor <;> rintro ⟨h1, h2⟩ <;> [exact ⟨(this.1 ⟨h1, h2.trans hh⟩).1, h2⟩;
    exact ⟨(this.2 ⟨h1, h2.trans hh⟩).1, h2⟩]

theorem mem_iff_of_ball_eq {U V : Set (FreeCox k)} {h : ℕ} (e : ball U h = ball V h)
    {x : FreeCox k} (hx : len x ≤ h) : x ∈ U ↔ x ∈ V := by
  have := Set.ext_iff.1 e x
  simp only [mem_ball] at this
  tauto

/-- `C(V, v)`: the colours of the edges incident to `v` in `Γ_k(V)`. -/
noncomputable def colours (V : Set (FreeCox k)) (v : FreeCox k) : Finset (Fin k) := by
  classical exact Finset.univ.filter (fun c => v * gen c ∈ V)

@[simp] theorem mem_colours {V : Set (FreeCox k)} {v : FreeCox k} {c : Fin k} :
    c ∈ colours V v ↔ v * gen c ∈ V := by
  classical simp [colours]

/-- A colour system is `d`-regular if every node has degree `d`. -/
def IsRegular (V : Set (FreeCox k)) (d : ℕ) : Prop := ∀ v ∈ V, (colours V v).card = d

theorem mem_inv_smul {V : Set (FreeCox k)} {u x : FreeCox k} : x ∈ u⁻¹ • V ↔ u * x ∈ V := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, smul_eq_mul]

theorem mem_smul {V : Set (FreeCox k)} {u x : FreeCox k} : x ∈ u • V ↔ u⁻¹ * x ∈ V := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]

theorem colours_inv_smul (V : Set (FreeCox k)) (u x : FreeCox k) :
    colours (u⁻¹ • V) x = colours V (u * x) := by
  ext c; simp [mem_inv_smul, mul_assoc]

/-! ### Prefixes -/

/-- `IsPre y x`: `y` lies on the path from `e` to `x` in `Γ_k`. -/
def IsPre (y x : FreeCox k) : Prop := len x = len y + len (y⁻¹ * x)

theorem isPre_refl (x : FreeCox k) : IsPre x x := by simp [IsPre]

theorem IsColourSystem.one_mem {V : Set (FreeCox k)} (hV : IsColourSystem V) :
    (1 : FreeCox k) ∈ V := hV.1

theorem IsColourSystem.mul_gen_mem {V : Set (FreeCox k)} (hV : IsColourSystem V) {x : FreeCox k}
    (hx : x ∈ V) {c : Fin k} (hc : len (x * gen c) < len x) : x * gen c ∈ V := hV.2 x hx c hc

/-- Colour systems are closed under prefixes. -/
theorem IsColourSystem.mem_of_isPre {V : Set (FreeCox k)} (hV : IsColourSystem V)
    {x y : FreeCox k} (hx : x ∈ V) (h : IsPre y x) : y ∈ V := by
  induction hn : len (y⁻¹ * x) generalizing x with
  | zero =>
    rw [len_eq_zero, inv_mul_eq_one] at hn
    rwa [hn]
  | succ n ih =>
    have hz : y⁻¹ * x ≠ 1 := by intro h1; rw [h1] at hn; simp at hn
    obtain ⟨c, hc⟩ := exists_mul_gen_lt hz
    have hc' := len_mul_gen_of_lt hc
    have h1 : len (x * gen c) ≤ len y + len (y⁻¹ * x * gen c) := by
      have := len_mul_le y (y⁻¹ * x * gen c)
      rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at this
    have h2 := le_len_mul_gen x c
    unfold IsPre at h
    have hlt : len (x * gen c) < len x := by omega
    refine ih (hV.mul_gen_mem hx hlt) ?_ (by rw [← mul_assoc]; omega)
    unfold IsPre; rw [← mul_assoc]; omega

/-- The key lemma behind Lemma 4 of [HirvonenSuomela2012]: walking from `u` towards `u w`, every
intermediate node `u w'` lies on the path from `e` to `u` or on the path from `e` to `u w`. -/
theorem isPre_or_isPre (u w : FreeCox k) (c : Fin k) (hw : len w < len (w * gen c)) :
    IsPre (u * w) u ∨ IsPre (u * w) (u * w * gen c) := by
  induction w using FreeCox.induction_on generalizing c with
  | h1 => left; simp [IsPre]
  | hstep w c' hw' ih =>
    -- m = u w c', b = m c, m' = u w
    by_cases hb : len (u * (w * gen c')) < len (u * (w * gen c') * gen c)
    · right
      unfold IsPre
      rw [inv_mul_cancel_left, len_gen]
      exact len_mul_gen_of_not_lt (by omega)
    · have hb' : len (u * (w * gen c') * gen c) < len (u * (w * gen c')) := by
        have := len_mul_gen_ne (u * (w * gen c')) c; omega
      -- `c ≠ c'`
      have hcc' : c ≠ c' := by
        rintro rfl
        rw [mul_gen_mul_gen] at hw
        omega
      -- the parent of `m = u w c'` is `m c`; so `m' = m c'` is a child of `m`
      have hm' : ¬ len (u * w * gen c' * gen c') < len (u * w * gen c') := by
        intro h
        exact hcc' (eq_of_len_mul_gen_lt (x := u * w * gen c') (by simpa [mul_assoc] using hb') h)
      rw [mul_gen_mul_gen] at hm'
      have hm'len : len (u * w) = len (u * w * gen c') + 1 := by
        have := len_mul_gen (u * w * gen c') c'
        rw [mul_gen_mul_gen] at this; omega
      rcases ih c' hw' with h | h
      · left
        unfold IsPre at h ⊢
        have e1 : (u * w)⁻¹ * u = w⁻¹ := by group
        have e2 : (u * (w * gen c'))⁻¹ * u = (w * gen c')⁻¹ := by group
        rw [e1, len_inv] at h
        rw [e2, len_inv, ← mul_assoc]
        have := len_mul_gen_of_not_lt (x := w) (c := c') (by omega)
        omega
      · exfalso
        unfold IsPre at h
        rw [inv_mul_cancel_left, len_gen] at h
        omega

/-- Lemma 4 of [HirvonenSuomela2012]: if `V` is a colour system and `u ∈ V`, then `ū V` is a colour
system. (The second half of Lemma 4, that `x ↦ ū x` is a colour-preserving isomorphism, is
`colours_inv_smul`.) -/
theorem IsColourSystem.inv_smul {V : Set (FreeCox k)} (hV : IsColourSystem V) {u : FreeCox k}
    (hu : u ∈ V) : IsColourSystem (u⁻¹ • V) := by
  refine ⟨by rwa [mem_inv_smul, mul_one], fun x hx c hc => ?_⟩
  rw [mem_inv_smul] at hx ⊢
  have h := isPre_or_isPre u (x * gen c) c (by rw [mul_gen_mul_gen]; exact hc)
  have e : u * (x * gen c) * gen c = u * x := by rw [mul_assoc, mul_gen_mul_gen]
  rw [e] at h
  rcases h with h | h
  · exact hV.mem_of_isPre hu h
  · exact hV.mem_of_isPre hx h

theorem IsColourSystem.mem_of_mul_mem {V : Set (FreeCox k)} (hV : IsColourSystem V)
    {u x : FreeCox k} (hu : u ∈ V) (hx : u * x ∈ V) {c : Fin k}
    (hc : len (x * gen c) < len x) : u * (x * gen c) ∈ V := by
  have := (hV.inv_smul hu).mul_gen_mem (mem_inv_smul.2 hx) hc
  rwa [mem_inv_smul] at this

theorem isRegular_inv_smul {V : Set (FreeCox k)} {d : ℕ} (hV : IsRegular V d) (u : FreeCox k) :
    IsRegular (u⁻¹ • V) d := by
  intro x hx
  rw [colours_inv_smul]
  exact hV _ (mem_inv_smul.1 hx)

theorem ball_ball (V : Set (FreeCox k)) (h : ℕ) : ball (ball V h) h = ball V h := by
  ext x; simp only [mem_ball]; tauto

theorem IsColourSystem.ball {V : Set (FreeCox k)} (hV : IsColourSystem V) (h : ℕ) :
    IsColourSystem (ball V h) :=
  ⟨⟨hV.one_mem, by simp⟩, fun x hx c hc => ⟨hV.mul_gen_mem hx.1 hc, by have := hx.2; omega⟩⟩

/-- Views of neighbours: radius `R + 1` around `e` determines radius `R` around `c`. -/
theorem ball_gen_inv_smul {U V : Set (FreeCox k)} {R : ℕ} (h : ball U (R + 1) = ball V (R + 1))
    (c : Fin k) : ball ((gen c)⁻¹ • U) R = ball ((gen c)⁻¹ • V) R := by
  ext z
  simp only [mem_ball, mem_inv_smul]
  refine and_congr_left fun hz => mem_iff_of_ball_eq h ?_
  have := len_gen_mul_le z c; omega

theorem ball_finite (V : Set (FreeCox k)) (h : ℕ) : (ball V h).Finite :=
  (finite_len_le h).subset (fun _ hx => hx.2)

end Cslib.ColourSystem
