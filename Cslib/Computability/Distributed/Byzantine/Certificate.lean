/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Foundations.Data.Finset.Quorum

/-!
# Threshold certificates

With ideal threshold signatures (or, equivalently, a set of authenticated messages), a value `x`
is *certified* with threshold `Q` when at least `Q` processes signed it. Processes are abstract:
`signed p x` is any relation, e.g. "`p` sent a vote for `x`", "`p` is Byzantine or a correct
replica that voted for `x`" (Byzantine processes can sign anything), or "a signature share of `p`
on `x` exists". The quorum facts of `Cslib.Foundations.Data.Finset.Quorum` then say that a
certificate has a correct signer and two certificates have a common correct signer.

## Main definitions

* `Cslib.Byzantine.signers signed x`: the processes that signed `x`.
* `Cslib.Byzantine.Certified signed Q x`: at least `Q` processes signed `x`.

## Main statements

* `Certified.mono`: certificates survive more signatures and a lower threshold.
* `Certified.exists_correct_signer`: with `f < Q`, a certificate has a signer outside any `F`
  with `#F ≤ f`.
* `Certified.common_correct_signer`: with `n + f < Q + Q'`, two certificates share a signer
  outside `F`.
* `certified_of_forall_notMem`: if every correct process signed `x`, then `x` is certified with
  threshold `n - f`.
-/

@[expose] public section

namespace Cslib.Byzantine

open Finset

variable {P X Y : Type*} [Fintype P] {signed : P → X → Prop} {signed' : P → Y → Prop}
  {F : Finset P} {f Q Q' : ℕ} {x : X} {y : Y}

/-- The processes that signed `x`. -/
noncomputable def signers (signed : P → X → Prop) (x : X) : Finset P := by
  classical exact {p | signed p x}

@[simp] theorem mem_signers {p : P} : p ∈ signers signed x ↔ signed p x := by
  classical simp [signers]

/-- `x` is certified with threshold `Q`: at least `Q` processes signed it. -/
def Certified (signed : P → X → Prop) (Q : ℕ) (x : X) : Prop := Q ≤ #(signers signed x)

theorem signers_mono {signed₂ : P → X → Prop} (h : ∀ p, signed p x → signed₂ p x) :
    signers signed x ⊆ signers signed₂ x := fun p => by simpa using h p

/-- A certificate remains valid when more processes sign and when the threshold decreases. -/
theorem Certified.mono {signed₂ : P → X → Prop} {Q₂ : ℕ} (hc : Certified signed Q x)
    (h : ∀ p, signed p x → signed₂ p x) (hQ : Q₂ ≤ Q) : Certified signed₂ Q₂ x :=
  hQ.trans (hc.trans (card_le_card (signers_mono h)))

/-- A certificate with threshold `Q > f` has a signer outside any `F` with `#F ≤ f`. -/
theorem Certified.exists_correct_signer (hc : Certified signed Q x) (hF : #F ≤ f) (hQ : f < Q) :
    ∃ p ∉ F, signed p x := by
  obtain ⟨p, hp, hpF⟩ := exists_mem_notMem_of_card_le_of_lt hF (hQ.trans_le hc)
  exact ⟨p, hpF, mem_signers.1 hp⟩

/-- Two certificates with thresholds `Q`, `Q'` and `n + f < Q + Q'` have a common signer outside
any `F` with `#F ≤ f`. -/
theorem Certified.common_correct_signer (hc : Certified signed Q x)
    (hc' : Certified signed' Q' y) (hF : #F ≤ f) (hn : Fintype.card P + f < Q + Q') :
    ∃ p ∉ F, signed p x ∧ signed' p y := by
  unfold Certified at hc hc'
  obtain ⟨p, hp, hp', hpF⟩ := exists_mem_inter_notMem_of_card_le
    (s := signers signed x) (t := signers signed' y) hF (by omega)
  exact ⟨p, hpF, mem_signers.1 hp, mem_signers.1 hp'⟩

/-- If every process outside `F` signed `x` and `#F ≤ f`, then `x` is certified with threshold
`n - f`. -/
theorem certified_of_forall_notMem (hF : #F ≤ f) (h : ∀ p ∉ F, signed p x) :
    Certified signed (Fintype.card P - f) x := by
  classical
  have := card_le_card (s := Fᶜ) fun p hp => mem_signers.2 (h p (mem_compl.1 hp))
  rw [card_compl] at this
  exact (by omega : Fintype.card P - f ≤ Fintype.card P - #F).trans this

end Cslib.Byzantine
