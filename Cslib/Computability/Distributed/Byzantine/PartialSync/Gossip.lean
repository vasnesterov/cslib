/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Auth

/-!
# Algorithms that gossip their knowledge

Authenticated protocols are often implemented by letting every process keep the set of all tokens
(signed statements) it has received or created, and send this set to everybody at every step;
certificates then travel with the statements that need them. This file proves, once and for all,
the generic facts about such algorithms in the partially synchronous model, for an abstract
*knowledge* `kn : S → Set K` (e.g. `kn s = ↑s.known`).

## Main definitions

* `Algorithm.SharesKnowledge A Au kn`: knowledge never shrinks, a process sends only tokens it
  knows, and it sends every token it knows to everybody (at every step).
* `Algorithm.Gossips A Au kn`: in addition, every received token is known after the step.

## Main statements

For a run `R`:
* `Run.honestTokens_origin` (for any unforging algorithm): in a run respecting unforgeability, a
  token emitted by a correct process is signed by a Byzantine process or was emitted by its signer
  itself, at the same time or earlier.
* `SharesKnowledge.unforging`: a knowledge-sharing algorithm that only adds own tokens and received
  tokens to its knowledge is unforging.
* `SharesKnowledge.mono`, `SharesKnowledge.subset_honestTokens`; with unforgeability:
  `SharesKnowledge.mem_of_mem_honestTokens`, `SharesKnowledge.mem_of_mem`,
  `SharesKnowledge.mem_of_mem_inbox` (a token known to, or received by, a correct process and
  signed by a correct `q` is known to `q` at the same time).
* `Gossips.subset_of_dl`, `Gossips.subset_of_valid`, `Gossips.subset_of_gst_le`: what a correct
  process knows is known to every correct process one step after delivery, hence within `δ + 1`
  after `max τ gst`.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

variable {P M S VI VO K : Type*}

/-- `A` *shares its knowledge* `kn`: knowledge never shrinks, a process sends only tokens it
knows, and it sends every token it knows to everybody. -/
structure Algorithm.SharesKnowledge (A : Algorithm P M S VI VO) (Au : Auth P M K)
    (kn : S → Set K) : Prop where
  /-- Knowledge never shrinks. -/
  subset_step : ∀ p s ib, kn s ⊆ kn (A.step p s ib)
  /-- A process sends only tokens it knows. -/
  tokens_subset : ∀ p s q, ∀ m ∈ A.send p s q, Au.tokens m ⊆ kn s
  /-- A process sends every token it knows to everybody. -/
  exists_mem_send : ∀ p s q, ∀ x ∈ kn s, ∃ m ∈ A.send p s q, x ∈ Au.tokens m

/-- `A` *gossips* its knowledge `kn`: it shares it and learns every received token. -/
structure Algorithm.Gossips (A : Algorithm P M S VI VO) (Au : Auth P M K) (kn : S → Set K) : Prop
    extends A.SharesKnowledge Au kn where
  /-- Every received token is known after the step. -/
  tokens_subset_step : ∀ p s ib q, ∀ m ∈ ib q, Au.tokens m ⊆ kn (A.step p s ib)

variable [DecidableEq P] {A : Algorithm P M S VI VO} {Au : Auth P M K} {R : Run P M VI}

/-- **Token origin.** In a run respecting unforgeability of an unforging algorithm, a token
emitted by a correct process by time `τ` is signed by a Byzantine process, or was emitted by its
(correct) signer itself by time `τ`. -/
theorem Run.honestTokens_origin (hU : A.Unforging Au) (hR : R.AuthValid Au A) {τ : ℕ} {x : K}
    (hx : x ∈ R.honestTokens Au A τ) :
    Au.signer x ∈ R.faulty ∨ ∃ τ' ≤ τ, ∃ r, ∃ m ∈ R.out A (Au.signer x) τ' r, x ∈ Au.tokens m := by
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    obtain ⟨τ₁, hτ₁, q, hq, r, m, hm, hxm⟩ := hx
    have hm' := hm
    rw [Run.out_of_correct A R hq] at hm'
    rcases hU R q τ₁ r m hm' x hxm with hs | ⟨τ₂, hτ₂, q', m', hm₂, hx₂⟩
    · exact Or.inr ⟨τ₁, hτ₁, r, m, hs ▸ hm, hxm⟩
    · obtain ⟨σ, hσ, -, hm₃⟩ := Run.mem_inbox.mp hm₂
      have hh : Au.signer x ∈ R.faulty ∨ x ∈ R.honestTokens Au A σ := by
        by_cases hq' : q' ∈ R.faulty
        · rw [Run.out_of_faulty A R hq'] at hm₃
          exact hR q' hq' σ q hq m' hm₃ x hx₂
        · exact Or.inr ⟨σ, le_rfl, q', hq', q, m', hm₃, hx₂⟩
      rcases hh with h | h
      · exact Or.inl h
      · rcases ih σ (by omega) h with h' | ⟨τ', hτ', r', m'', hm'', hx''⟩
        · exact Or.inl h'
        · exact Or.inr ⟨τ', by omega, r', m'', hm'', hx''⟩

namespace Algorithm.SharesKnowledge

variable {kn : S → Set K} (h : A.SharesKnowledge Au kn)
include h

/-- Knowledge grows along every run. -/
theorem mono (R : Run P M VI) {τ τ' : ℕ} (hτ : τ ≤ τ') (p : P) :
    kn (R.st A τ p) ⊆ kn (R.st A τ' p) := by
  induction hτ with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (by rw [Run.st_succ]; exact h.subset_step _ _ _)

/-- A correct process sends only tokens it knows. -/
theorem tokens_subset_of_mem_out {q : P} (hq : q ∉ R.faulty) {τ : ℕ} {r : P} {m : M}
    (hm : m ∈ R.out A q τ r) : Au.tokens m ⊆ kn (R.st A τ q) := by
  rw [Run.out_of_correct A R hq] at hm
  exact h.tokens_subset _ _ _ m hm

/-- What a correct process knows, it has emitted. -/
theorem subset_honestTokens {q : P} (hq : q ∉ R.faulty) (τ : ℕ) :
    kn (R.st A τ q) ⊆ R.honestTokens Au A τ := fun x hx => by
  obtain ⟨m, hm, hxm⟩ := h.exists_mem_send q _ q x hx
  exact ⟨τ, le_rfl, q, hq, q, m, by rw [Run.out_of_correct A R hq]; exact hm, hxm⟩

/-- A knowledge-sharing algorithm that only adds its own tokens and received tokens to its
knowledge is unforging. -/
theorem unforging (hinit : ∀ p v, ∀ x ∈ kn (A.init p v), Au.signer x = p)
    (hstep : ∀ p s ib, ∀ x ∈ kn (A.step p s ib),
      x ∈ kn s ∨ (∃ q, ∃ m ∈ ib q, x ∈ Au.tokens m) ∨ Au.signer x = p) :
    A.Unforging Au := by
  intro R p τ q m hm x hx
  suffices H : ∀ τ, ∀ x ∈ kn (R.st A τ p), Au.signer x = p ∨ x ∈ R.recvTokens Au A p τ from
    H τ x (h.tokens_subset _ _ _ m hm hx)
  intro τ
  induction τ with
  | zero => exact fun x hx => Or.inl (hinit p _ x hx)
  | succ τ ih =>
    intro x hx
    rw [Run.st_succ] at hx
    rcases hstep _ _ _ x hx with hx | ⟨r, m, hm, hxm⟩ | hs
    · rcases ih x hx with h' | ⟨τ', hτ', rest⟩
      · exact Or.inl h'
      · exact Or.inr ⟨τ', by omega, rest⟩
    · exact Or.inr ⟨τ, by omega, r, m, hm, hxm⟩
    · exact Or.inl hs

variable (hU : A.Unforging Au) (hR : R.AuthValid Au A)
include hU hR

/-- A token emitted by correct processes and signed by a correct `q` is known to `q`. -/
theorem mem_of_mem_honestTokens {q : P} (hq : q ∉ R.faulty) {τ : ℕ} {x : K}
    (hx : x ∈ R.honestTokens Au A τ) (hs : Au.signer x = q) : x ∈ kn (R.st A τ q) := by
  rcases Run.honestTokens_origin hU hR hx with hf | ⟨τ', hτ', r, m, hm, hxm⟩
  · exact absurd (hs ▸ hf) hq
  · rw [hs] at hm
    exact h.mono R hτ' q (h.tokens_subset_of_mem_out hq hm hxm)

/-- A token known to a correct process and signed by a correct `q` is known to `q`. -/
theorem mem_of_mem {c q : P} (hc : c ∉ R.faulty) (hq : q ∉ R.faulty) {τ : ℕ} {x : K}
    (hx : x ∈ kn (R.st A τ c)) (hs : Au.signer x = q) : x ∈ kn (R.st A τ q) :=
  h.mem_of_mem_honestTokens hU hR hq (h.subset_honestTokens hc τ hx) hs

/-- A token received by a correct process at time `τ` and signed by a correct `q` is known to
`q` at time `τ`. -/
theorem mem_of_mem_inbox {c q : P} (hc : c ∉ R.faulty) (hq : q ∉ R.faulty) {τ : ℕ} {r : P}
    {m : M} (hm : m ∈ R.inbox A c τ r) {x : K} (hx : x ∈ Au.tokens m) (hs : Au.signer x = q) :
    x ∈ kn (R.st A τ q) := by
  obtain ⟨σ, hσ, -, hm'⟩ := Run.mem_inbox.mp hm
  refine h.mono R hσ q (h.mem_of_mem_honestTokens hU hR hq ?_ hs)
  by_cases hr : r ∈ R.faulty
  · rw [Run.out_of_faulty _ _ hr] at hm'
    rcases hR r hr σ c hc m hm' x hx with hf | hx'
    · exact absurd (hs ▸ hf) hq
    · exact hx'
  · exact ⟨σ, le_rfl, r, hr, c, m, hm', hx⟩

end Algorithm.SharesKnowledge

namespace Algorithm.Gossips

variable {kn : S → Set K} (h : A.Gossips Au kn)
include h

/-- Received tokens are known after the step. -/
theorem tokens_subset_of_mem_inbox {p : P} {τ : ℕ} {r : P} {m : M} (hm : m ∈ R.inbox A p τ r) :
    Au.tokens m ⊆ kn (R.st A (τ + 1) p) := by
  rw [Run.st_succ]
  exact h.tokens_subset_step _ _ _ r m hm

/-- **Gossip.** What a correct process `q` knows at `τ` is known to `r` right after the delivery
of `q`'s batch of time `τ`. -/
theorem subset_of_dl {q r : P} (hq : q ∉ R.faulty) {τ : ℕ} (hdl : τ ≤ R.dl q τ r) :
    kn (R.st A τ q) ⊆ kn (R.st A (R.dl q τ r + 1) r) := fun x hx => by
  obtain ⟨m, hm, hxm⟩ := h.exists_mem_send q _ r x hx
  refine h.tokens_subset_of_mem_inbox (Run.mem_inbox.mpr ⟨τ, hdl, rfl, ?_⟩) hxm
  rw [Run.out_of_correct A R hq]
  exact hm

/-- **Gossip in partial synchrony.** What a correct process knows at `τ` is known to every correct
process at `max τ gst + δ + 1`. -/
theorem subset_of_valid {t δ : ℕ} (hR : R.Valid t δ) {q r : P} (hq : q ∉ R.faulty)
    (hr : r ∉ R.faulty) (τ : ℕ) : kn (R.st A τ q) ⊆ kn (R.st A (max τ R.gst + δ + 1) r) :=
  (h.subset_of_dl hq (hR.dl_ge q τ r hq hr)).trans
    (h.toSharesKnowledge.mono R (by have := hR.dl_le q τ r hq hr; omega) r)

/-- **Gossip after GST.** What a correct process knows at `τ ≥ gst` is known to every correct
process at `τ + δ + 1`. -/
theorem subset_of_gst_le {t δ : ℕ} (hR : R.Valid t δ) {q r : P} (hq : q ∉ R.faulty)
    (hr : r ∉ R.faulty) {τ : ℕ} (hτ : R.gst ≤ τ) : kn (R.st A τ q) ⊆ kn (R.st A (τ + δ + 1) r) := by
  simpa [max_eq_left hτ] using h.subset_of_valid hR hq hr τ

end Algorithm.Gossips

end Cslib.Byzantine.PartialSync
