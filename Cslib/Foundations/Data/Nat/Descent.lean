/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Order.OrderIsoNat

/-!
# Eventually non-increasing sequences of natural numbers

A sequence `f : ℕ → ℕ` that is non-increasing from some index `N` on is eventually constant
(`Nat.eventually_const_of_succ_le`); consequently it can decrease only finitely often
(`Nat.eventually_not_of_succ_le`, `Nat.not_frequently_lt_of_succ_le`). These are the termination
arguments ("potential functions") behind wait-freedom and lock-freedom proofs. Dually, a bounded
sequence that is non-decreasing from some index on is eventually constant
(`Nat.eventually_const_of_le_succ`).

`Nat.exists_lt_and_not_succ_of_not` is the discrete intermediate value property used in valency
arguments ("the last configuration along an execution from which `v` can still be decided");
`Nat.exists_last_of_le` gives the last index of an interval at which a property holds.

Both follow from Mathlib's antitone chain condition (`WellFoundedLT.antitone_chain_condition`).
-/

@[expose] public section

namespace Nat

variable {f : ℕ → ℕ} {N : ℕ}

/-- A sequence of natural numbers that is non-increasing from `N` on is eventually constant. -/
theorem eventually_const_of_succ_le (h : ∀ m ≥ N, f (m + 1) ≤ f m) :
    ∃ T ≥ N, ∀ m ≥ T, f m = f T := by
  obtain ⟨n, hn⟩ := WellFoundedLT.antitone_chain_condition (f := fun k => f (N + k))
    (antitone_nat_of_succ_le fun k => h (N + k) (by omega))
  refine ⟨N + n, by omega, fun m hm => ?_⟩
  have := hn (m - N) (by omega)
  rw [show N + (m - N) = m by omega] at this
  exact this.symm

/-- A sequence of natural numbers that is non-increasing from `N` on and strictly decreases at
every index `m ≥ N` satisfying `p m` satisfies `p` only finitely often. -/
theorem eventually_not_of_succ_le (h : ∀ m ≥ N, f (m + 1) ≤ f m) {p : ℕ → Prop}
    (hp : ∀ m ≥ N, p m → f (m + 1) < f m) : ∃ T ≥ N, ∀ m ≥ T, ¬ p m := by
  obtain ⟨T, hT, hc⟩ := eventually_const_of_succ_le h
  refine ⟨T, hT, fun m hm hpm => ?_⟩
  have := hp m (by omega) hpm
  rw [hc m hm, hc (m + 1) (by omega)] at this
  exact lt_irrefl _ this

/-- A sequence of natural numbers that is non-increasing from `N` on cannot decrease infinitely
often. -/
theorem not_frequently_lt_of_succ_le (h : ∀ m ≥ N, f (m + 1) ≤ f m) :
    ¬ ∀ M, ∃ m ≥ M, f (m + 1) < f m := by
  intro hs
  obtain ⟨T, hT, hc⟩ := eventually_not_of_succ_le h (p := fun m => f (m + 1) < f m)
    fun _ _ hm => hm
  obtain ⟨m, hm, hlt⟩ := hs T
  exact hc m hm hlt

/-- A bounded sequence of natural numbers that is non-decreasing from `N` on is eventually
constant. -/
theorem eventually_const_of_le_succ {B : ℕ} (hB : ∀ m ≥ N, f m ≤ B)
    (h : ∀ m ≥ N, f m ≤ f (m + 1)) : ∃ T ≥ N, ∀ m ≥ T, f m = f T := by
  obtain ⟨T, hT, hc⟩ := eventually_const_of_succ_le (f := fun m => B - f m) (N := N)
    fun m hm => by have := h m hm; have := hB m hm; have := hB (m + 1) (by omega); omega
  refine ⟨T, hT, fun m hm => ?_⟩
  have := hc m hm; have := hB m (by omega); have := hB T hT
  omega

/-- **Discrete intermediate value property.** If `p 0` holds and `p K` fails, then there is a
last index `m < K` at which `p` holds before failing at `m + 1`. -/
theorem exists_lt_and_not_succ_of_not {p : ℕ → Prop} {K : ℕ} (h0 : p 0) (hK : ¬ p K) :
    ∃ m < K, p m ∧ ¬ p (m + 1) := by
  induction K with
  | zero => exact absurd h0 hK
  | succ K ih =>
    by_cases hp : p K
    · exact ⟨K, K.lt_succ_self, hp, hK⟩
    · obtain ⟨m, hm, h⟩ := ih hp
      exact ⟨m, by omega, h⟩

/-- **Last index.** If `p a` holds and `a ≤ b`, there is a last index `m ∈ [a, b]` at which `p`
holds: `p` fails on `(m, b]`. -/
theorem exists_last_of_le {p : ℕ → Prop} {a b : ℕ} (hab : a ≤ b) (ha : p a) :
    ∃ m, a ≤ m ∧ m ≤ b ∧ p m ∧ ∀ k, m < k → k ≤ b → ¬ p k := by
  classical
  have hs := Nat.findGreatest_spec (P := fun k => a ≤ k ∧ p k) hab ⟨le_rfl, ha⟩
  refine ⟨_, hs.1, Nat.findGreatest_le b, hs.2, fun k hk hkb hpk => ?_⟩
  exact Nat.findGreatest_is_greatest hk hkb ⟨hs.1.trans hk.le, hpk⟩

end Nat
