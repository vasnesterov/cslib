/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Agreement.AttiyaWelch.Protocol

/-! # The Attiya–Welch graded consensus protocol AW′: safety

Safety of AW′ (`Cslib.Distributed.AttiyaWelch.protocol`) for `3t < n`: strong validity,
consistency, proposal validity (from which external validity follows) and integrity. The proofs
follow the structure of AW's safety argument: values echoed or approved by correct processes were
proposed by correct processes, and at most one value of `Value` (the *leg*) occurs among the
`ECHO_3`, `ECHO_4` and `ECHO_5` messages of correct processes.

## Main definitions

* `AttiyaWelch.Unanimous ρ v`: all proposals of correct processes are `v`.
* `AttiyaWelch.Leg ρ x`: some correct process sent `ECHO_3 (some x)`.

## Main statements

* `echo_origin`, `approval_origin`: echoed and approved values were proposed by correct
  processes.
* `unanimity_decide`: strong validity.
* `quo_unique`: two correct processes cannot hold quorums of `ECHO_k`, `k ≠ 1`, for different
  values.
* `Leg.eq`: there is at most one leg.
* `proposal_validity`, `consistency`, `atMostOnce` (integrity), `decide_after_propose`.

## References

* [P. Civit, M. A. Dzulfikar, S. Gilbert, R. Guerraoui, J. Komatovic, M. Vidigueira,
  I. Zablotchi, *Partial Synchrony for Free? New Upper Bounds for Byzantine Agreement*,
  arXiv:2402.10059][CivitEtAl2024]
* [H. Attiya, J. L. Welch, *Multi-Valued Connected Consensus: A New Perspective on Crusader
  Agreement and Adopt-Commit*, OPODIS 2023][AttiyaWelch2023]
-/

@[expose] public section

namespace Cslib.Distributed

namespace AttiyaWelch

open GradedConsensus Finset

variable {P Value : Type} [DecidableEq P] [DecidableEq Value] [Fintype P]

/-! ### Safety -/

section Safety

variable {t δ : ℕ} {ρ : Run (protocol P Value t)} {p q : P} {τ τ' : ℕ} {k : Phase}
  {a b : Option Value} {v w x y : Value} {g : Bool}

omit [DecidableEq P] [DecidableEq Value] in
theorem lt_card_of_quo (hn : 3 * t < Fintype.card P) {R : Msg Value → Finset P}
    (h : Quo t R k a) : t < #(R (.echo k a)) := by
  unfold Quo at h
  omega

/-- *Echo origin*: if a correct process sends `ECHO_1 (some x)` at time `τ`, some
correct process proposed `x` before `τ` (more than `t` processes sent it `INIT x`). -/
theorem echo_origin (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty)
    (h : SendAll ρ p (.echo .one (some x)) τ) :
    ∃ q ∉ ρ.faulty, ∃ τ' < τ, .req (.propose x) ∈ ρ.input q τ' := by
  obtain ⟨q, hq, τ', hτ', hs⟩ := exists_correct_of_lt_card hρ hp (cand_of_sendAll h)
  exact ⟨q, hq, τ', by omega, propose_of_sendAll_init hs⟩

/-- *Approval origin*: a value approved by a correct process was proposed by a
correct process. -/
theorem approval_origin (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P) (hp : p ∉ ρ.faulty)
    (h : Quo t (ρ.state p τ).rcv .one (some x)) :
    ∃ q ∉ ρ.faulty, ∃ τ' < τ, .req (.propose x) ∈ ρ.input q τ' := by
  obtain ⟨q, hq, τ', hτ', hs⟩ := exists_correct_of_lt_card hρ hp (lt_card_of_quo hn h)
  obtain ⟨r, hr, τ'', hτ'', hreq⟩ := echo_origin hρ hq hs
  exact ⟨r, hr, τ'', by omega, hreq⟩

/-! #### Unanimity -/

section Unanimity

/-- All proposals of correct processes are `v`. -/
abbrev Unanimous (ρ : Run (protocol P Value t)) (v : Value) : Prop :=
  ∀ q ∉ ρ.faulty, ∀ w τ, .req (.propose w) ∈ ρ.input q τ → w = v

/-- Under unanimity, correct processes only send `ECHO_1 (some v)`. -/
theorem unanimity_echo_one (hρ : ρ.Valid t δ) (hU : Unanimous ρ v) (hp : p ∉ ρ.faulty)
    (h : SendAll ρ p (.echo .one a) τ) : a = some v := by
  induction τ using Nat.strong_induction_on generalizing p a with
  | _ τ ih =>
  have hc := cand_of_sendAll h
  cases a with
  | some x =>
    obtain ⟨q, hq, τ', -, hs⟩ := exists_correct_of_lt_card hρ hp hc
    rw [hU q hq x τ' (propose_of_sendAll_init hs)]
  | none =>
    exfalso
    rcases hc with h' | h' | ⟨a, b, hab, ha, hb⟩
    · -- `Evid` fails at `v`: only faulty processes send `INIT`s with other values
      obtain ⟨S, hS, hS'⟩ := h' v
      have hSF : S ⊆ ρ.faulty := by
        intro q hq
        by_contra hqF
        obtain ⟨y, hy, hq'⟩ := hS' q hq
        obtain ⟨τ', -, hs⟩ := exists_sendAll_of_mem_rcv hρ hp hqF hq'
        exact hy (hU q hqF y τ' (propose_of_sendAll_init hs))
      have := card_le_card hSF
      have := hρ.card_faulty_le
      omega
    · obtain ⟨q, hq, τ', hτ', hs⟩ := exists_correct_of_lt_card hρ hp h'
      exact absurd (ih τ' (by omega) hq hs) (by simp)
    · -- two different values echoed by correct processes
      obtain ⟨q, hq, τ', hτ', hs⟩ := exists_correct_of_lt_card hρ hp ha
      obtain ⟨q', hq', τ'', hτ'', hs'⟩ := exists_correct_of_lt_card hρ hp hb
      exact hab ((ih τ' (by omega) hq hs).trans (ih τ'' (by omega) hq' hs').symm)

/-- Under unanimity, correct processes only approve `some v`. -/
theorem unanimity_quo_one (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    (hU : Unanimous ρ v) (hp : p ∉ ρ.faulty) (h : Quo t (ρ.state p τ).rcv .one a) :
    a = some v := by
  obtain ⟨q, hq, τ', -, hs⟩ := exists_correct_of_lt_card hρ hp (lt_card_of_quo hn h)
  exact unanimity_echo_one hρ hU hq hs

/-- Under unanimity, `AC` never holds at a correct process. -/
theorem unanimity_not_ac (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    (hU : Unanimous ρ v) (hp : p ∉ ρ.faulty) : ¬ AC t (ρ.state p τ).rcv := by
  rintro (⟨a, b, hab, ha, hb⟩ | h)
  · exact hab ((unanimity_quo_one hρ hn hU hp ha).trans (unanimity_quo_one hρ hn hU hp hb).symm)
  · exact absurd (unanimity_quo_one hρ hn hU hp h) (by simp)

/-- Under unanimity, correct processes only send `ECHO_k (some v)`. -/
theorem unanimity_echo (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P) (hU : Unanimous ρ v)
    (hp : p ∉ ρ.faulty) (h : SendAll ρ p (.echo k a) τ) : a = some v := by
  have hq : ∀ {k}, (∀ {p τ a}, p ∉ ρ.faulty → SendAll ρ p (.echo k a) τ → a = some v) →
      ∀ {p τ a}, p ∉ ρ.faulty → Quo t (ρ.state p τ).rcv k a → a = some v := by
    intro k hk p τ a hp h
    obtain ⟨q, hq, τ', -, hs⟩ := exists_correct_of_lt_card hρ hp (lt_card_of_quo hn h)
    exact hk hq hs
  have h2 : ∀ {p τ a}, p ∉ ρ.faulty → SendAll ρ p (.echo .two a) τ → a = some v :=
    fun hp h => unanimity_quo_one hρ hn hU hp (cand_of_sendAll h)
  have h3 : ∀ {p τ a}, p ∉ ρ.faulty → SendAll ρ p (.echo .three a) τ → a = some v := by
    intro p τ a hp h
    rcases cand_of_sendAll h with h' | ⟨-, h'⟩
    · exact hq h2 hp h'
    · exact absurd h' (unanimity_not_ac hρ hn hU hp)
  have h4 : ∀ {p τ a}, p ∉ ρ.faulty → SendAll ρ p (.echo .four a) τ → a = some v := by
    intro p τ a hp h
    rcases cand_of_sendAll h with ⟨-, -, h'⟩ | h'
    · exact absurd h' (unanimity_not_ac hρ hn hU hp)
    · exact hq h3 hp h'
  cases k with
  | one => exact unanimity_echo_one hρ hU hp h
  | two => exact h2 hp h
  | three => exact h3 hp h
  | four => exact h4 hp h
  | five =>
    rcases cand_of_sendAll h with h' | ⟨-, -, h'⟩
    · exact hq h4 hp h'
    · exact absurd h' (unanimity_not_ac hρ hn hU hp)

/-- Under unanimity, correct processes only decide `(v, 1)`. -/
theorem unanimity_decide (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P) (hU : Unanimous ρ v)
    (hp : p ∉ ρ.faulty) (h : .ind (.decide w g) ∈ ρ.output p τ) : w = v ∧ g = true := by
  obtain ⟨-, hd⟩ := dec_of_ind h
  cases g with
  | true =>
    obtain ⟨q, hq, τ', -, hs⟩ := exists_correct_of_lt_card hρ hp (lt_card_of_quo hn hd)
    exact ⟨Option.some.inj (unanimity_echo hρ hn hU hq hs), rfl⟩
  | false =>
    exfalso
    rcases hd with ⟨-, hac, -, -⟩ | ⟨hd, -⟩
    · exact unanimity_not_ac hρ hn hU hp hac
    · obtain ⟨q, hq, τ', -, hs⟩ := exists_correct_of_lt_card hρ hp (lt_card_of_quo hn hd)
      exact absurd (unanimity_echo hρ hn hU hq hs) (by simp)

end Unanimity

/-- *Unique quorum value* in phases `k ≠ 1` (for `k = 5` and values `some x` and `⊥`: *centre
exclusion*): two correct processes cannot hold quorums of `ECHO_k` for different values. -/
theorem quo_unique (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P) (hk : k ≠ .one) {p' : P}
    (hp : p ∉ ρ.faulty) (hp' : p' ∉ ρ.faulty) (h : Quo t (ρ.state p τ).rcv k a)
    (h' : Quo t (ρ.state p' τ').rcv k b) : a = b := by
  obtain ⟨r, hr, ⟨τ₁, h₁⟩, τ₂, h₂⟩ := exists_correct_of_quorums hρ hn hp hp' h h'
  exact (sendAll_echo_unique hk h₁ h₂).1

/-! #### Single leg -/

variable (ρ) in
/-- `Leg ρ x`: some correct process sent `ECHO_3 (some x)`. -/
def Leg (x : Value) : Prop := ∃ q ∉ ρ.faulty, ∃ τ, SendAll ρ q (.echo .three (some x)) τ

/-- A process sends `ECHO_3 (some x)` only via the E2-branch. -/
theorem quo_two_of_sendAll_three (h : SendAll ρ q (.echo .three (some x)) τ) :
    Quo t (ρ.state q (τ + 1)).rcv .two (some x) := by
  rcases cand_of_sendAll h with h' | ⟨h', -⟩
  · exact h'
  · cases h'

/-- *Single leg*: there is at most one leg. -/
theorem Leg.eq (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P) (hx : Leg ρ x)
    (hy : Leg ρ y) : x = y := by
  obtain ⟨p, hp, τ, h⟩ := hx
  obtain ⟨q, hq, τ', h'⟩ := hy
  exact Option.some.inj (quo_unique hρ hn (by decide) hp hq (quo_two_of_sendAll_three h)
    (quo_two_of_sendAll_three h'))

/-- A leg was proposed by a correct process. -/
theorem Leg.exists_propose (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P) (hx : Leg ρ x) :
    ∃ q ∉ ρ.faulty, ∃ τ, .req (.propose x) ∈ ρ.input q τ := by
  obtain ⟨p, hp, τ, h⟩ := hx
  obtain ⟨q, hq, τ', -, hs⟩ :=
    exists_correct_of_lt_card hρ hp (lt_card_of_quo hn (quo_two_of_sendAll_three h))
  obtain ⟨r, hr, τ'', -, hreq⟩ := approval_origin hρ hn hq (cand_of_sendAll hs)
  exact ⟨r, hr, τ'', hreq⟩

theorem leg_of_lt_card_three (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty)
    (h : t < #((ρ.state p τ).rcv (.echo .three (some x)))) : Leg ρ x := by
  obtain ⟨q, hq, τ', -, hs⟩ := exists_correct_of_lt_card hρ hp h
  exact ⟨q, hq, τ', hs⟩

/-- A correct `ECHO_4 (some x)` implies the leg `x`. -/
theorem leg_of_sendAll_four (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    (hp : p ∉ ρ.faulty) (h : SendAll ρ p (.echo .four (some x)) τ) : Leg ρ x := by
  rcases cand_of_sendAll h with ⟨h', -⟩ | h'
  · cases h'
  · exact leg_of_lt_card_three hρ hp (lt_card_of_quo hn h')

/-- More than `t` recorded `ECHO_4 (some x)` (as for a D1-decision) imply the leg `x`. -/
theorem leg_of_lt_card_four (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    (hp : p ∉ ρ.faulty) (h : t < #((ρ.state p τ).rcv (.echo .four (some x)))) : Leg ρ x := by
  obtain ⟨q, hq, τ', -, hs⟩ := exists_correct_of_lt_card hρ hp h
  exact leg_of_sendAll_four hρ hn hq hs

/-- A correct `ECHO_5 (some x)` implies the leg `x`. -/
theorem leg_of_sendAll_five (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    (hp : p ∉ ρ.faulty) (h : SendAll ρ p (.echo .five (some x)) τ) : Leg ρ x := by
  rcases cand_of_sendAll h with h' | ⟨h', -⟩
  · exact leg_of_lt_card_four hρ hn hp (lt_card_of_quo hn h')
  · cases h'

/-- A quorum of `ECHO_5 (some x)` (as for a D2-decision) implies the leg `x`. -/
theorem leg_of_quo_five (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    (hp : p ∉ ρ.faulty) (h : Quo t (ρ.state p τ).rcv .five (some x)) : Leg ρ x := by
  obtain ⟨q, hq, τ', -, hs⟩ := exists_correct_of_lt_card hρ hp (lt_card_of_quo hn h)
  exact leg_of_sendAll_five hρ hn hq hs

/-- Among the `ECHO_k` messages sent by correct processes, `k ∈ {3, 4, 5}`, at most one value
of `Value` occurs. -/
theorem sendAll_some_eq (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    (hk : k = .three ∨ k = .four ∨ k = .five) (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty)
    (h : SendAll ρ p (.echo k (some x)) τ) (h' : SendAll ρ q (.echo k (some y)) τ') : x = y := by
  have leg : ∀ {p x τ}, p ∉ ρ.faulty → SendAll ρ p (.echo k (some x)) τ → Leg ρ x := by
    intro p x τ hp h
    rcases hk with rfl | rfl | rfl
    exacts [⟨p, hp, τ, h⟩, leg_of_sendAll_four hρ hn hp h, leg_of_sendAll_five hρ hn hp h]
  exact (leg hp h).eq hρ hn (leg hq h')

/-- If two correct processes send `ECHO_k` messages with different values,
`k ∈ {3, 4, 5}`, then one of the values is `⊥`. -/
theorem sendAll_eq_none_or (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P)
    (hk : k = .three ∨ k = .four ∨ k = .five) (hp : p ∉ ρ.faulty) (hq : q ∉ ρ.faulty)
    (h : SendAll ρ p (.echo k a) τ) (h' : SendAll ρ q (.echo k b) τ') (hne : a ≠ b) :
    a = none ∨ b = none := by
  rcases a with _ | x
  · exact .inl rfl
  rcases b with _ | y
  · exact .inr rfl
  exact absurd (congrArg some (sendAll_some_eq hρ hn hk hp hq h h')) hne

/-! #### Theorems -/

/-- *Decide only after proposing* (not required by the specification): a correct process
decides only after it has proposed. -/
theorem decide_after_propose (hρ : ρ.Valid t δ) (hp : p ∉ ρ.faulty)
    (h : .ind (.decide v g) ∈ ρ.output p τ) : ∃ w, ∃ τ' < τ, .req (.propose w) ∈ ρ.input p τ' := by
  obtain ⟨⟨x, hx⟩, -⟩ := dec_of_ind h
  obtain ⟨τ', hτ', hs⟩ := exists_sendAll_of_mem_rcv hρ hp hp hx
  exact ⟨x, τ', by omega, propose_of_sendAll_init hs⟩

/-- *Proposal validity* (the additional *Safety* property of AW in [CivitEtAl2024], appendix
"Existing primitives"): a value decided by a correct process was proposed by a correct process. -/
theorem proposal_validity (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P) (hp : p ∉ ρ.faulty)
    (h : .ind (.decide x g) ∈ ρ.output p τ) :
    ∃ q ∉ ρ.faulty, ∃ τ', .req (.propose x) ∈ ρ.input q τ' := by
  obtain ⟨-, hd⟩ := dec_of_ind h
  cases g with
  | true => exact (leg_of_quo_five hρ hn hp hd).exists_propose hρ hn
  | false =>
    rcases hd with ⟨-, -, -, h4⟩ | ⟨-, hi⟩
    · exact (leg_of_lt_card_four hρ hn hp h4).exists_propose hρ hn
    · obtain ⟨τ', -, hs⟩ := exists_sendAll_of_mem_rcv hρ hp hp hi
      exact ⟨p, hp, τ', propose_of_sendAll_init hs⟩

/-- *Consistency*: if a correct process decides `(v, 1)`, every decision of a
correct process has value `v`. -/
theorem consistency (hρ : ρ.Valid t δ) (hn : 3 * t < Fintype.card P) (hp : p ∉ ρ.faulty)
    (hq : q ∉ ρ.faulty) (h₁ : .ind (.decide v true) ∈ ρ.output p τ)
    (h₂ : .ind (.decide w g) ∈ ρ.output q τ') : w = v := by
  obtain ⟨-, hd₁⟩ := dec_of_ind h₁
  have hv := leg_of_quo_five hρ hn hp hd₁
  obtain ⟨-, hd₂⟩ := dec_of_ind h₂
  cases g with
  | true => exact (leg_of_quo_five hρ hn hq hd₂).eq hρ hn hv
  | false =>
    rcases hd₂ with ⟨-, -, -, h4⟩ | ⟨h0, -⟩
    · exact (leg_of_lt_card_four hρ hn hq h4).eq hρ hn hv
    · exact absurd (quo_unique hρ hn (by decide) hp hq hd₁ h0) (by simp)

end Safety

/-! ### Integrity -/

/-- **Integrity**: every process (correct or not, by construction) emits at most one decision,
since deciding sets the once-only flag `dec`. -/
theorem atMostOnce {t : ℕ} (ρ : Run (protocol P Value t)) (p : P)
    {b : Event (interface Value) → Bool} (hreq : ∀ r, b (.req r) = false)
    (hind : ∀ i, b (.ind i) = true) : ρ.history.AtMostOnce p b := by
  refine Run.atMostOnce_of_flag (fun s => s.dec.isSome) (by simp)
    (fun _ _ _ h => dec_isSome_step.2 (.inl h)) fun _ x s h => ?_
  simp only [countP_stepEvents hreq hind] at h ⊢
  obtain ⟨_, hi⟩ := List.length_pos_iff_exists_mem.1 h
  obtain ⟨_, ho, hi⟩ := List.mem_filterMap.1 hi
  obtain rfl := Output.ind?_eq_some_iff.1 hi
  obtain ⟨q, m, rfl, hab, hd⟩ := ind_mem_step.1 ho
  exact ⟨by simp [(newDec_eq_some hd).1], dec_isSome_step.2 (.inr ⟨q, m, rfl, hab, by simp [hd]⟩),
    length_filterMap_ind?_step_le⟩

end AttiyaWelch

end Cslib.Distributed
