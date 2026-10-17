/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Rounds
public import Cslib.Computability.Distributed.Byzantine.PartialSync.Auth

/-!
# Signatures in the round layer

Transport of the token model of signatures (`Auth.lean`) through the round layer
(`Rounds.lean`), so that authenticated protocols can be verified against the abstract
`RoundRun` and then compiled into the time-based model.

* `Auth.tagged Au`: the signature structure on round-tagged messages `ℕ × Msg` (the tag carries
  no token).
* `RoundAlgorithm.Unforging RA Au`: in every abstract round execution, a process only sends
  tokens it signed itself or tokens it received in an earlier round.
* `RoundRun.AuthValid Au E`: every message received by a correct process in round `r` carries
  only tokens of faulty signers or tokens sent by correct processes in rounds `≤ r` (rushing,
  eavesdropping adversary).
* `RoundAlgorithm.compile_unforging`: an unforging round algorithm compiles to an unforging
  algorithm; `Run.toRoundRun_authValid`: the round execution induced by an `AuthValid` run is
  `AuthValid`.
* `RoundRun.tokens_origin`, `RoundRun.tokens_origin_rcv`: **unforgeability at the round level** —
  a token of a correct signer `s` that is sent or received by a correct process in round `r` was
  sent by `s` itself in some round `≤ r`.
* `RoundRun.sync_empty_authValid`: without faulty processes, the synchronous round execution
  respects unforgeability.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

variable {P Msg S VI VO K : Type*} [DecidableEq P]

/-- Signature structure on round-tagged messages: the tokens of `(r, m)` are those of `m`. -/
def Auth.tagged (Au : Auth P Msg K) : Auth P (ℕ × Msg) K where
  signer := Au.signer
  tokens m := Au.tokens m.2

/-- A round algorithm is *unforging* if, in every round execution, a process only sends tokens it
signed or tokens received in an earlier round. -/
def RoundAlgorithm.Unforging (RA : RoundAlgorithm P Msg S VI VO) (Au : Auth P Msg K) : Prop :=
  ∀ (F : Finset P) (inp : P → VI) (E : RoundRun RA F inp) r p q m,
    RA.send r p (E.s r p) q = some m → ∀ x ∈ Au.tokens m,
      Au.signer x = p ∨ ∃ r' < r, ∃ q' m', E.rcv r' p q' = some m' ∧ x ∈ Au.tokens m'

/-- The adversary of a round execution respects unforgeability: a message received by a correct
process in round `r` only carries tokens of faulty signers, or tokens sent by correct processes in
rounds `≤ r`. -/
def RoundRun.AuthValid {RA : RoundAlgorithm P Msg S VI VO} {F : Finset P} {inp : P → VI}
    (Au : Auth P Msg K) (E : RoundRun RA F inp) : Prop :=
  ∀ r p q m, p ∉ F → E.rcv r p q = some m → ∀ x ∈ Au.tokens m,
    Au.signer x ∈ F ∨
      ∃ r' ≤ r, ∃ q' ∉ F, ∃ w m', RA.send r' q' (E.s r' q') w = some m' ∧ x ∈ Au.tokens m'

namespace RoundRun

variable {RA : RoundAlgorithm P Msg S VI VO} {F : Finset P} {inp : P → VI} {Au : Auth P Msg K}
  (E : RoundRun RA F inp)

omit [DecidableEq P] in
/-- **Unforgeability.** A token of a correct signer sent by a correct process in round `r` was
sent by its signer in some round `≤ r`. -/
theorem tokens_origin (hU : RA.Unforging Au) (hA : E.AuthValid Au) :
    ∀ r q, q ∉ F → ∀ w m, RA.send r q (E.s r q) w = some m → ∀ x ∈ Au.tokens m,
      Au.signer x ∉ F → ∃ r' ≤ r, ∃ w' m',
        RA.send r' (Au.signer x) (E.s r' (Au.signer x)) w' = some m' ∧ x ∈ Au.tokens m' := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro q hq w m hm x hx hs
    rcases hU F inp E r q w m hm x hx with h | ⟨r1, hr1, q1, m1, hm1, hx1⟩
    · subst h; exact ⟨r, le_rfl, w, m, hm, hx⟩
    · rcases hA r1 q q1 m1 hq hm1 x hx1 with h | ⟨r2, hr2, q2, hq2, w2, m2, hm2, hx2⟩
      · exact absurd h hs
      · obtain ⟨r', hr', w', m', h'⟩ := ih r2 (by omega) q2 hq2 w2 m2 hm2 x hx2 hs
        exact ⟨r', by omega, w', m', h'⟩

omit [DecidableEq P] in
/-- **Unforgeability.** A token of a correct signer received by a correct process in round `r`
was sent by its signer in some round `≤ r`. -/
theorem tokens_origin_rcv (hU : RA.Unforging Au) (hA : E.AuthValid Au) {r : ℕ} {p q : P}
    (hp : p ∉ F) {m : Msg} (hm : E.rcv r p q = some m) {x : K} (hx : x ∈ Au.tokens m)
    (hs : Au.signer x ∉ F) : ∃ r' ≤ r, ∃ w' m',
      RA.send r' (Au.signer x) (E.s r' (Au.signer x)) w' = some m' ∧ x ∈ Au.tokens m' := by
  rcases hA r p q m hp hm x hx with h | ⟨r2, hr2, q2, hq2, w2, m2, hm2, hx2⟩
  · exact absurd h hs
  · obtain ⟨r', hr', w', m', h'⟩ := E.tokens_origin hU hA r2 q2 hq2 w2 m2 hm2 x hx2 hs
    exact ⟨r', by omega, w', m', h'⟩

end RoundRun

namespace Run

variable {RA : RoundAlgorithm P Msg S VI VO} {L : ℕ} (R : Run P (ℕ × Msg) VI)

private theorem mul_add_div_of_lt' {r L i : ℕ} (hi : i < L) : (r * L + i) / L = r := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]

/-- Buffered messages were received (with the tag of the current round) earlier in the round. -/
theorem newBuf_compile_mem (hL : 0 < L) (τ : ℕ) {p q : P} {m : Msg}
    (h : RoundAlgorithm.newBuf L (R.st (RA.compile L) τ p) (R.inbox (RA.compile L) p τ) q =
      some m) :
    ∃ σ ≤ τ, (τ / L, m) ∈ R.inbox (RA.compile L) p σ q := by
  induction τ generalizing m with
  | zero =>
    rcases newBuf_cases h with hb | hi
    · simp [RoundAlgorithm.compile] at hb
    · rw [clock_st_compile] at hi
      exact ⟨0, le_rfl, hi⟩
  | succ τ ih =>
    rcases newBuf_cases h with hb | hi
    · rw [st_succ_compile] at hb
      split_ifs at hb with hτ
      have hd : (τ + 1) / L = τ / L := by
        have h1 := Nat.div_add_mod' τ L
        have h2 := Nat.mod_lt τ hL
        rw [show τ + 1 = τ / L * L + (τ % L + 1) by omega, mul_add_div_of_lt' (by omega)]
      rw [hd]
      obtain ⟨σ, hσ, h⟩ := ih hb
      exact ⟨σ, by omega, h⟩
    · rw [clock_st_compile] at hi
      exact ⟨τ + 1, le_rfl, hi⟩

/-- The round execution induced by a run respecting unforgeability respects unforgeability. -/
theorem toRoundRun_authValid {Au : Auth P Msg K} (hL : 0 < L)
    (hRa : R.AuthValid Au.tagged (RA.compile L)) : (R.toRoundRun RA L hL).AuthValid Au := by
  intro r p q m hp hm x hx
  by_cases hq : q ∈ R.faulty
  · obtain ⟨σ, hσ, hmem⟩ := R.newBuf_compile_mem hL _ hm
    rw [mul_add_div_of_lt' (by omega)] at hmem
    obtain ⟨σ', hσ', -, hout⟩ := mem_inbox.mp hmem
    rw [out_of_faulty _ _ hq] at hout
    rcases hRa q hq σ' p hp (r, m) hout x hx with h | ⟨τ', hτ', q', hq', w, m'', hm'', hx''⟩
    · exact Or.inl h
    · right
      rw [out_of_correct _ _ hq', compile_send, clock_st_compile] at hm''
      split_ifs at hm'' with h0
      swap; · simp at hm''
      simp only [Option.mem_toList, Option.map_eq_some_iff] at hm''
      obtain ⟨m3, hs3, rfl⟩ := hm''
      have hτ : τ' / L * L = τ' := by have := Nat.div_add_mod' τ' L; omega
      have hr : τ' / L ≤ r := by
        have : τ' / L < r + 1 := by
          rw [Nat.div_lt_iff_lt_mul hL, Nat.succ_mul]; omega
        omega
      refine ⟨τ' / L, hr, q', hq', w, m3, ?_, hx''⟩
      change RA.send (τ' / L) q' (R.st (RA.compile L) (τ' / L * L) q').s w = some m3
      rw [hτ]; exact hs3
  · exact Or.inr ⟨r, le_rfl, q, hq, p, m, (R.toRoundRun RA L hL).honest r p q m hq hm, hx⟩

end Run

/-- An unforging round algorithm compiles to an unforging algorithm (for tagged messages). -/
theorem RoundAlgorithm.compile_unforging {RA : RoundAlgorithm P Msg S VI VO} {Au : Auth P Msg K}
    {L : ℕ} (hL : 0 < L) (hU : RA.Unforging Au) : (RA.compile L).Unforging Au.tagged := by
  intro R p τ q m hm x hx
  rw [Run.compile_send, Run.clock_st_compile] at hm
  split_ifs at hm with h0
  swap; · simp at hm
  simp only [Option.mem_toList, Option.map_eq_some_iff] at hm
  obtain ⟨m', hs, rfl⟩ := hm
  have hτ : τ / L * L = τ := by have := Nat.div_add_mod' τ L; omega
  have hs' : RA.send (τ / L) p ((R.toRoundRun RA L hL).s (τ / L) p) q = some m' := by
    change RA.send (τ / L) p (R.st (RA.compile L) (τ / L * L) p).s q = some m'
    rw [hτ]; exact hs
  rcases hU _ _ _ _ p q m' hs' x hx with h | ⟨r', hr', q', m'', hm'', hx''⟩
  · exact Or.inl h
  · right
    obtain ⟨σ, hσ, hmem⟩ := R.newBuf_compile_mem hL _ hm''
    refine ⟨σ, ?_, q', _, hmem, hx''⟩
    have : r' * L + (L - 1) < τ / L * L := by
      have : (r' + 1) * L ≤ τ / L * L := Nat.mul_le_mul_right _ hr'
      rw [Nat.succ_mul] at this; omega
    omega

namespace RoundRun

variable (RA : RoundAlgorithm P Msg S VI VO) (inp : P → VI)
  (adv : ℕ → (P → S) → P → P → Option Msg)

/-- Without faulty processes, the synchronous execution respects unforgeability. -/
theorem sync_empty_authValid (Au : Auth P Msg K) : (sync RA ∅ inp adv).AuthValid Au := by
  intro r p q m _ hm x hx
  simp only [sync, Finset.notMem_empty, ite_false] at hm
  exact Or.inr ⟨r, le_rfl, q, Finset.notMem_empty q, p, m, hm, hx⟩

end RoundRun

end Cslib.Byzantine.PartialSync
