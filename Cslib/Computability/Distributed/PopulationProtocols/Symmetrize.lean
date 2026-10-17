/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.PopulationProtocols.Basic

/-! # Ordered-pair fairness and symmetrization

For asymmetric protocols (only the initiator changes in some rules) the two readings of weak
fairness differ: unordered pairs (`Execution.WeaklyFair`) vs. ordered pairs
(`Execution.OrderedFair`: every agent initiates with every other agent infinitely often).
The symmetrization `P.symm` performs `δ` with both role assignments; a weakly fair execution of
`P.symm` unfolds into an ordered-fair execution of `P` (`Execution.WeaklyFair.unfold`), which
transfers correctness proofs from `P` under ordered fairness to `P.symm` under weak fairness.
-/

@[expose] public section

namespace Cslib.PopulationProtocol.Protocol

variable {Q A : Type*} [DecidableEq A] {P : Protocol Q}

/-- Weak fairness for ordered pairs: every agent `a` interacts infinitely often as the initiator
with every other agent `b` as the responder. -/
def Execution.OrderedFair (E : P.Execution A) : Prop :=
  ∀ a b, a ≠ b → ∀ T, ∃ t ≥ T, E.sched t = (a, b)

lemma Execution.OrderedFair.weaklyFair {E : P.Execution A} (h : E.OrderedFair) :
    E.WeaklyFair := fun a b hab T => by
  obtain ⟨t, ht, hs⟩ := h a b hab T
  exact ⟨t, ht, Or.inl hs⟩

/-- A shifted execution: `E.shift T` starts at time `T` of `E`. -/
def Execution.shift (E : P.Execution A) (T : ℕ) : P.Execution A where
  config t := E.config (T + t)
  sched t := E.sched (T + t)
  sched_ne t := E.sched_ne (T + t)
  step t := E.step (T + t)

/-! ### Symmetrization -/

/-- The symmetrization of `P`: the initiator/responder transition `δ`, followed by `δ` with the
roles swapped. -/
def symm (P : Protocol Q) : Protocol Q :=
  ⟨fun p q => ((P.δ (P.δ p q).2 (P.δ p q).1).2, (P.δ (P.δ p q).2 (P.δ p q).1).1)⟩

lemma symm_interact (C : Config A Q) {a b : A} (hab : a ≠ b) :
    P.symm.interact C a b = P.interact (P.interact C a b) b a := by
  funext x
  by_cases hxa : x = a
  · subst hxa
    simp [interact, symm, hab, Ne.symm hab]
  · by_cases hxb : x = b
    · subst hxb
      simp [interact, symm, Ne.symm hab]
    · simp [interact, hxa, hxb]

/-- Unfolding an execution of `P.symm` into an execution of `P` (twice as many steps). -/
def Execution.unfold (E : P.symm.Execution A) : P.Execution A where
  config t := if t % 2 = 0 then E.config (t / 2) else
    P.interact (E.config (t / 2)) (E.sched (t / 2)).1 (E.sched (t / 2)).2
  sched t := if t % 2 = 0 then E.sched (t / 2) else ((E.sched (t / 2)).2, (E.sched (t / 2)).1)
  sched_ne t := by
    split_ifs
    · exact E.sched_ne _
    · exact Ne.symm (E.sched_ne _)
  step t := by
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have h1 : (t + 1) % 2 = 1 := by omega
      have h2 : (t + 1) / 2 = t / 2 := by omega
      simp only [h, h1, h2, ite_true]
      simp
    · have h1 : (t + 1) % 2 = 0 := by omega
      have h2 : (t + 1) / 2 = t / 2 + 1 := by omega
      simp only [h, h1, h2, ite_true, one_ne_zero, ite_false]
      rw [E.step, symm_interact _ (E.sched_ne _)]

lemma Execution.unfold_even (E : P.symm.Execution A) (t : ℕ) :
    E.unfold.config (2 * t) = E.config t := by
  simp [Execution.unfold]

lemma Execution.unfold_zero (E : P.symm.Execution A) : E.unfold.config 0 = E.config 0 :=
  E.unfold_even 0

/-- Weak fairness (unordered pairs) of an execution of `P.symm` gives ordered fairness of its
unfolding. -/
lemma Execution.WeaklyFair.unfold {E : P.symm.Execution A} (h : E.WeaklyFair) :
    E.unfold.OrderedFair := by
  intro a b hab T
  obtain ⟨t, ht, hs⟩ := h a b hab T
  rcases hs with hs | hs
  · refine ⟨2 * t, by omega, ?_⟩
    simp [Execution.unfold, hs]
  · refine ⟨2 * t + 1, by omega, ?_⟩
    have h1 : (2 * t + 1) % 2 = 1 := by omega
    have h2 : (2 * t + 1) / 2 = t := by omega
    simp [Execution.unfold, h1, h2, hs]

/-- Eventual properties of the unfolding hold for the original execution. -/
lemma Execution.eventually_of_unfold {E : P.symm.Execution A} {p : Config A Q → Prop}
    (h : ∃ T, ∀ t ≥ T, p (E.unfold.config t)) : ∃ T, ∀ t ≥ T, p (E.config t) := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun t ht => by rw [← E.unfold_even]; exact hT _ (by omega)⟩

end Cslib.PopulationProtocol.Protocol
