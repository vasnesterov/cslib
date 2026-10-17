/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.LockStep.Cover
public import Cslib.Computability.Distributed.Byzantine.Auth

/-!
# Authenticated setting (ideal unforgeable signatures)

We model ideal signatures abstractly by *tokens* (`Cslib.Byzantine.Auth`): every message `m : M`
contains a set of signature tokens `A.tokens m : Set S`, and every token has a signer
`A.signer τ : P`. Unforgeability is a
restriction on who may emit a token:

* honest parties (`Protocol.Unforging`): a party only emits tokens it signed itself or tokens that
  occur in its history (it may relay signatures it has seen);
* Byzantine parties (`Scenario.AuthValid`): a Byzantine message to an honest party only contains
  tokens of Byzantine signers, or tokens that honest parties have emitted in this or an earlier
  round (to anybody — the adversary may eavesdrop — and including the current round — the adversary
  is rushing). This is the strongest standard adversary of the authenticated synchronous model.

What a token "says" (its payload) is up to the concrete message type: tokens are opaque here. Since
the token type `S` is part of the protocol, protocols can use separate token types for separate
purposes (domain separation by typing).
-/

@[expose] public section

namespace Cslib.Byzantine.LockStep

/-- An abstract signature structure on messages (the model-independent `Cslib.Byzantine.Auth`). -/
abbrev Auth (P M S : Type*) := Byzantine.Auth P M S

variable {P I M O S Q : Type*}

namespace Auth

variable (A : Auth P M S)

/-- Tokens occurring in a history. -/
def histTokens (h : History P M) : Set S :=
  {τ | ∃ ib ∈ h, ∃ p m, ib p = some m ∧ τ ∈ A.tokens m}

lemma histTokens_append (h₁ h₂ : History P M) :
    A.histTokens (h₁ ++ h₂) = A.histTokens h₁ ∪ A.histTokens h₂ := by
  ext τ; simp only [histTokens, List.mem_append, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨ib, hib | hib, rest⟩
    · exact Or.inl ⟨ib, hib, rest⟩
    · exact Or.inr ⟨ib, hib, rest⟩
  · rintro (⟨ib, hib, rest⟩ | ⟨ib, hib, rest⟩)
    · exact ⟨ib, Or.inl hib, rest⟩
    · exact ⟨ib, Or.inr hib, rest⟩

/-- The trivial signature structure (no tokens): every protocol is unforging for it. -/
abbrev none (P M : Type*) : Auth P M Empty := Byzantine.Auth.none P M

end Auth

/-- Honest parties only emit their own signatures and signatures they have received. -/
def Protocol.Unforging (A : Auth P M S) (alg : Protocol P I M O) : Prop :=
  ∀ p x h q m, alg.send p x h q = some m → ∀ τ ∈ A.tokens m, A.signer τ = p ∨ τ ∈ A.histTokens h

lemma Protocol.unforging_none (alg : Protocol P I M O) : alg.Unforging (Auth.none P M) := by
  intro _ _ _ _ _ _ τ; exact τ.elim

variable (G : SimpleGraph P) (alg : Protocol P I M O) (A : Auth P M S)

/-- Tokens emitted by honest parties in rounds `≤ r`. -/
def honestTokens (s : Scenario P I M) (r : ℕ) : Set S :=
  {τ | ∃ r' ≤ r, ∃ p, p ∉ s.byz ∧ ∃ q, G.Adj p q ∧ ∃ m,
    alg.send p (s.input p) (hist G alg s r' p) q = some m ∧ τ ∈ A.tokens m}

lemma honestTokens_mono (s : Scenario P I M) {r r' : ℕ} (h : r ≤ r') :
    honestTokens G alg A s r ⊆ honestTokens G alg A s r' := by
  rintro τ ⟨r₀, hr₀, rest⟩; exact ⟨r₀, hr₀.trans h, rest⟩

/-- The adversary of `s` respects unforgeability. -/
def Scenario.AuthValid (s : Scenario P I M) : Prop :=
  ∀ r b q m, b ∈ s.byz → q ∉ s.byz → G.Adj b q → s.adv r b q = some m →
    ∀ τ ∈ A.tokens m, A.signer τ ∈ s.byz ∨ τ ∈ honestTokens G alg A s r

/-- `alg` solves `spec` in the authenticated setting. -/
def SolvesAuth (Z : AdvStructure P) (spec : Spec P I O) : Prop :=
  ∀ s : Scenario P I M, s.byz ∈ Z → s.Reliable → s.AuthValid G alg A →
    spec s.input s.honest (Decides G alg s)

/-- Solvability in the authenticated synchronous model: some unforging protocol, with some message
and token types, solves the problem against all unforgeability-respecting adversaries. -/
def SolvableAuth (G : SimpleGraph P) (Z : AdvStructure P) (spec : Spec P I O) : Prop :=
  ∃ (M S : Type) (A : Auth P M S) (alg : Protocol P I M O),
    alg.Unforging A ∧ SolvesAuth G alg A Z spec

lemma Solves.solvesAuth {Z : AdvStructure P} {spec : Spec P I O} (h : Solves G alg Z spec) :
    SolvesAuth G alg A Z spec := fun s hZ hrel _ => h s hZ hrel

/-- Unauthenticated solvability implies authenticated solvability. -/
lemma Solvable.solvableAuth {Z : AdvStructure P} {spec : Spec P I O} (h : Solvable G Z spec) :
    SolvableAuth G Z spec := by
  obtain ⟨M, alg, h⟩ := h
  exact ⟨M, Empty, Auth.none P M, alg, alg.unforging_none, h.solvesAuth G alg _⟩

namespace CoverSystem

variable {G alg A}
variable (C : CoverSystem P I Q) {B : Set P} {σ : P → Q}

/-- In a covering system where every node an honest-adjacent node listens to is either a lift of an
honest party or a copy of a Byzantine party, the simulating adversary is unforgeability-respecting:
Byzantine parties only ever need their own signatures and signatures relayed from honest parties. -/
theorem scenario_authValid (hU : alg.Unforging A) (hL : C.Lift G B σ)
    (hφ : ∀ q p q', C.nbr q p = some q' → C.φ q' = p)
    (hsim : ∀ q p q', G.Adj p (C.φ q) → C.nbr q p = some q' →
      (∃ p', p' ∉ B ∧ q' = σ p') ∨ C.φ q' ∈ B)
    (x₀ : P → I) : (C.scenario G alg B σ x₀).AuthValid G alg A := by
  set s := C.scenario G alg B σ x₀
  -- every token in a covering history is Byzantine-signed or emitted by an honest party
  have key : ∀ r q, A.histTokens (C.hist G alg r q) ⊆
      {τ | A.signer τ ∈ B} ∪ honestTokens G alg A s r := by
    intro r
    induction r with
    | zero => intro q τ hτ; simp [CoverSystem.hist, Auth.histTokens] at hτ
    | succ r ih =>
      intro q τ hτ
      rw [CoverSystem.hist, Auth.histTokens_append] at hτ
      rcases hτ with hτ | hτ
      · rcases ih q hτ with h | h
        · exact Or.inl h
        · exact Or.inr (honestTokens_mono G alg A s (Nat.le_succ r) h)
      · obtain ⟨ib, hib, p, m, hm, hτm⟩ := hτ
        simp only [List.mem_singleton] at hib
        subst hib
        by_cases hadj : G.Adj p (C.φ q)
        · simp only [hadj, ite_true] at hm
          obtain ⟨q', hq', hm'⟩ := Option.bind_eq_some_iff.mp hm
          have hφq' := hφ q p q' hq'
          rcases hsim q p q' hadj hq' with ⟨p', hp', rfl⟩ | hB
          · -- the sender is the lift of an honest party: its message is a real honest message
            have hpp' : p' = p := by rw [← hL.φ_σ p' hp']; exact hφq'
            subst hpp'
            refine Or.inr ⟨r, Nat.le_succ r, p', hp', C.φ q, hadj, m, ?_, hτm⟩
            rw [CoverSystem.hist_scenario C hL x₀ r p' hp',
              CoverSystem.scenario_input_of_not_mem C x₀ hp']
            rw [hL.φ_σ p' hp'] at hm'; exact hm'
          · rcases hU _ _ _ _ _ hm' τ hτm with hs | hs
            · exact Or.inl (show A.signer τ ∈ B by rw [hs]; exact hB)
            · rcases ih q' hs with h | h
              · exact Or.inl h
              · exact Or.inr (honestTokens_mono G alg A s (Nat.le_succ r) h)
        · simp [hadj] at hm
  intro r b q m hb hq _ hm τ hτ
  simp only [s, CoverSystem.scenario] at hm
  obtain ⟨q', hq', hm⟩ := Option.bind_eq_some_iff.mp hm
  have hφq' : C.φ q' = b := hφ _ _ _ hq'
  rcases hU _ _ _ _ _ hm τ hτ with hs | hs
  · exact Or.inl (show A.signer τ ∈ _ by rw [hs, hφq']; exact hb)
  · exact key r q' hs

end CoverSystem

/-! ### Input translation in the authenticated setting -/

section comap

variable {G alg A}

lemma Protocol.Unforging.comapInput {I' : Type*} (hU : alg.Unforging A) (f : I' → I) :
    (alg.comapInput f).Unforging A := fun p x h q m hm => hU p (f x) h q m hm

lemma honestTokens_comapInput {I' : Type*} (f : I' → I) (s : Scenario P I' M) (r : ℕ) :
    honestTokens G (alg.comapInput f) A s r = honestTokens G alg A (s.mapInput f) r := by
  simp only [honestTokens, hist_comapInput]
  rfl

lemma Scenario.authValid_comapInput {I' : Type*} (f : I' → I) (s : Scenario P I' M) :
    s.AuthValid G (alg.comapInput f) A ↔ (s.mapInput f).AuthValid G alg A := by
  simp only [Scenario.AuthValid, honestTokens_comapInput]
  rfl

end comap

end Cslib.Byzantine.LockStep
