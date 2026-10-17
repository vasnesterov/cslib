/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.Congest.LowerBound
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Gathering the whole graph: every graph predicate is decidable in `n` rounds


The full-information algorithm `gatherAlg P`: every node keeps the set of nodes whose neighbourhood
it knows, together with those neighbourhoods, and forwards everything in each round. On a
connected graph with `n` nodes, after `n` rounds every node knows the whole graph and accepts iff
`P G`. Messages have `B = ⌈log₂ |(V → Bool) × (V → V → Bool)|⌉ = n + n²` bits.

This shows that the hypotheses of the lower bounds in
`Cslib.Computability.Distributed.Congest.LowerBound` ("an algorithm decides `P` in `T` rounds on the
family") are satisfiable — the lower bounds are not vacuous.
-/

@[expose] public section

namespace Cslib.Congest

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Knowledge of a node: which neighbourhoods it knows, and the adjacency rows it knows. -/
abbrev Know (V : Type*) := (V → Bool) × (V → V → Bool)

/-- Number of message bits of the gathering algorithm. -/
noncomputable def gatherBits (V : Type*) [Fintype V] [DecidableEq V] : ℕ :=
  Nat.clog 2 (Fintype.card (Know V))

/-- Binary encoding of the knowledge into `gatherBits V` bits. -/
noncomputable def encK : Know V → Msg (gatherBits V) := fun k =>
  (Fintype.equivFin (Msg (gatherBits V))).symm
    (Fin.castLE (by
      have : Fintype.card (Msg (gatherBits V)) = 2 ^ gatherBits V := by simp [Msg]
      rw [this]
      exact Nat.le_pow_clog (by norm_num) _) (Fintype.equivFin (Know V) k))

/-- The encoding of knowledge is injective. -/
lemma encK_injective : Function.Injective (encK (V := V)) := by
  intro a b h
  simp only [encK, EmbeddingLike.apply_eq_iff_eq, Fin.castLE_inj] at h
  exact h

/-- Decoding (a left inverse of `encK`). -/
noncomputable def decK : Msg (gatherBits V) → Know V := Function.invFun encK

/-- Decoding inverts encoding. -/
lemma decK_encK (k : Know V) : decK (encK k) = k := Function.leftInverse_invFun encK_injective k

/-- The full-information gathering algorithm deciding a predicate of the adjacency matrix. -/
noncomputable def gatherAlg (P : (V → V → Bool) → Prop) :
    Algorithm V (V → Bool) (Know V) (gatherBits V) := by
  classical
  exact
  { init := fun v r => (fun a => decide (a = v), fun a b => decide (a = v) && r b)
    send := fun _ k _ => encK k
    step := fun _ k m =>
      (fun a => k.1 a || decide (∃ u, ∃ c, m u = some c ∧ (decK c).1 a = true),
        fun a b => k.2 a b || decide (∃ u, ∃ c, m u = some c ∧ (decK c).2 a b = true))
    out := fun _ k => decide ((∀ a, k.1 a = true) ∧ P k.2) }

variable (P : (V → V → Bool) → Prop) (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A node accepts iff it knows every neighbourhood and the known adjacency rows satisfy `P`. -/
lemma gatherAlg_out (v : V) (k : Know V) :
    (gatherAlg P).out v k = true ↔ (∀ a, k.1 a = true) ∧ P k.2 := by
  simp [gatherAlg]

/-- The input of a node: its neighbourhood. -/
def adjInput : V → V → Bool := fun v w => decide (G.Adj v w)

/-- Invariant: after `t` rounds node `v` knows the neighbourhood of `a` iff `a` is within distance
`t`, and its rows are exact. -/
lemma gather_run (t : ℕ) (v : V) :
    (∀ a, ((gatherAlg P).run G (adjInput G) t v).1 a = true ↔
      ∃ p : G.Walk v a, p.length ≤ t) ∧
    (∀ a b, ((gatherAlg P).run G (adjInput G) t v).2 a b = true ↔
      (∃ p : G.Walk v a, p.length ≤ t) ∧ G.Adj a b) := by
  classical
  induction t generalizing v with
  | zero =>
    simp only [Algorithm.run, gatherAlg, adjInput, Bool.and_eq_true, decide_eq_true_eq,
      nonpos_iff_eq_zero]
    constructor
    · intro a
      constructor
      · rintro rfl; exact ⟨.nil, rfl⟩
      · rintro ⟨p, hp⟩; exact (SimpleGraph.Walk.eq_of_length_eq_zero hp).symm
    · intro a b
      constructor
      · rintro ⟨rfl, h⟩; exact ⟨⟨.nil, rfl⟩, h⟩
      · rintro ⟨⟨p, hp⟩, h⟩
        obtain rfl := SimpleGraph.Walk.eq_of_length_eq_zero hp
        exact ⟨rfl, h⟩
  | succ t ih =>
    have hreach : ∀ a, (∃ p : G.Walk v a, p.length ≤ t + 1) ↔
        (∃ p : G.Walk v a, p.length ≤ t) ∨ ∃ u, G.Adj u v ∧ ∃ p : G.Walk u a, p.length ≤ t := by
      intro a
      constructor
      · rintro ⟨p, hp⟩
        cases p with
        | nil => exact Or.inl ⟨.nil, by simp⟩
        | cons h q =>
          right
          exact ⟨_, h.symm, q, by simp at hp; omega⟩
      · rintro (⟨p, hp⟩ | ⟨u, hu, p, hp⟩)
        · exact ⟨p, by omega⟩
        · exact ⟨.cons hu.symm p, by simp; omega⟩
    have hmsg : ∀ (Q : Know V → Prop) (u : V),
        (∃ c, (if G.Adj u v then some (encK ((gatherAlg P).run G (adjInput G) t u))
          else none) = some c ∧ Q (decK c)) ↔
          G.Adj u v ∧ Q ((gatherAlg P).run G (adjInput G) t u) := by
      intro Q u
      by_cases hu : G.Adj u v
      · simp only [hu, ↓reduceIte, Option.some.injEq, true_and]
        constructor
        · rintro ⟨c, rfl, hc⟩; rwa [decK_encK] at hc
        · intro h; exact ⟨_, rfl, by rwa [decK_encK]⟩
      · simp [hu]
    have e1 : ∀ a, ((gatherAlg P).run G (adjInput G) (t + 1) v).1 a = true ↔
        ((gatherAlg P).run G (adjInput G) t v).1 a = true ∨
          ∃ u, G.Adj u v ∧ ((gatherAlg P).run G (adjInput G) t u).1 a = true := by
      intro a
      simp only [Algorithm.run, gatherAlg, Bool.or_eq_true, decide_eq_true_eq]
      exact or_congr Iff.rfl (exists_congr fun u => hmsg (fun k => k.1 a = true) u)
    have e2 : ∀ a b, ((gatherAlg P).run G (adjInput G) (t + 1) v).2 a b = true ↔
        ((gatherAlg P).run G (adjInput G) t v).2 a b = true ∨
          ∃ u, G.Adj u v ∧ ((gatherAlg P).run G (adjInput G) t u).2 a b = true := by
      intro a b
      simp only [Algorithm.run, gatherAlg, Bool.or_eq_true, decide_eq_true_eq]
      exact or_congr Iff.rfl (exists_congr fun u => hmsg (fun k => k.2 a b = true) u)
    refine ⟨fun a => ?_, fun a b => ?_⟩
    · rw [e1, hreach, (ih v).1]
      exact or_congr Iff.rfl (exists_congr fun u => and_congr Iff.rfl ((ih u).1 a))
    · rw [e2, (ih v).2, hreach, or_and_right]
      refine or_congr Iff.rfl ⟨?_, ?_⟩
      · rintro ⟨u, hu, h⟩
        rw [(ih u).2] at h
        exact ⟨⟨u, hu, h.1⟩, h.2⟩
      · rintro ⟨⟨u, hu, hp⟩, hab⟩
        exact ⟨u, hu, ((ih u).2 a b).2 ⟨hp, hab⟩⟩

/-- **Gathering decides every predicate of the adjacency matrix on connected graphs** within
`|V|` rounds, with `n + n²`-bit messages (`gatherBits V`). -/
theorem gather_accepts (hG : G.Connected) :
    (gatherAlg P).Accepts G (adjInput G) (Fintype.card V) ↔ P (adjInput G) := by
  classical
  have hall : ∀ v a, ∃ p : G.Walk v a, p.length ≤ Fintype.card V := by
    intro v a
    obtain ⟨p⟩ := hG.preconnected v a
    exact ⟨p.bypass, (p.bypass_isPath.length_lt).le⟩
  have hk : ∀ v, ((gatherAlg P).run G (adjInput G) (Fintype.card V) v).1 = fun _ => true := by
    intro v; funext a; exact ((gather_run P G (Fintype.card V) v).1 a).2 (hall v a)
  have hadj : ∀ v, ((gatherAlg P).run G (adjInput G) (Fintype.card V) v).2 = adjInput G := by
    intro v; funext a b
    have := (gather_run P G (Fintype.card V) v).2 a b
    simp only [hall v a, true_and] at this
    cases h : ((gatherAlg P).run G (adjInput G) (Fintype.card V) v).2 a b <;>
      simp_all [adjInput]
  obtain ⟨v₀⟩ := hG.nonempty
  simp only [Algorithm.Accepts, gatherAlg_out, hk, hadj, implies_true, true_and]
  exact ⟨fun h => h v₀, fun h _ => h⟩

omit [Fintype V] [DecidableEq V] in
/-- The graph is recovered from the adjacency inputs. -/
lemma fromRel_adjInput : SimpleGraph.fromRel (fun a b => adjInput G a b = true) = G := by
  ext a b
  simp only [SimpleGraph.fromRel_adj, adjInput, decide_eq_true_eq, ne_eq]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact h.symm
  · intro h; exact ⟨G.ne_of_adj h, Or.inl h⟩

/-- Gathering decides every graph property `Q` on connected graphs in `|V|` rounds. -/
theorem gather_accepts_graph (Q : SimpleGraph V → Prop) (hG : G.Connected) :
    (gatherAlg fun M => Q (SimpleGraph.fromRel fun a b => M a b = true)).Accepts G (adjInput G)
      (Fintype.card V) ↔ Q G := by
  rw [gather_accepts _ G hG, fromRel_adjInput]

end Cslib.Congest
