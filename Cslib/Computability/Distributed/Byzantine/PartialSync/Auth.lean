/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Constructions

/-!
# Authenticated setting (ideal unforgeable signatures) for the partially synchronous model

Same design as `Cslib.Byzantine.LockStep.Auth` (Byzantine-Stable-Matching agent): signatures are
abstract *tokens*. Every message `m` carries a set of tokens `Au.tokens m`, every token has a
signer `Au.signer x : P`. Unforgeability restricts who may emit a token:

* algorithms (`Algorithm.Unforging`): in every run, a process only sends tokens it signed itself
  or tokens it has received before (it may relay signatures it has seen);
* the adversary (`Run.AuthValid`): a Byzantine message to a correct process only contains tokens
  of Byzantine signers, or tokens that correct processes have emitted (to anybody: the adversary
  eavesdrops) at the same time or earlier (the adversary is rushing).

The unauthenticated model is the special case `Auth.none` (no tokens): every algorithm is
unforging and every run is `AuthValid`.

The main tool is `Run.tokens_replay`: when a constructed run `R'` lets Byzantine processes replay
messages of a reference run `Ri`, those replays respect unforgeability, provided every process
either behaves in `R'` as in `Ri`, or is Byzantine in `R'` and correct in `Ri`, or only emits
tokens of `R'`-Byzantine signers in `Ri`.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S VI VO K : Type*} [DecidableEq P]

/-- An abstract signature structure on messages. -/
structure Auth (P M K : Type*) where
  /-- The signer of a token. -/
  signer : K → P
  /-- The signature tokens contained in a message. -/
  tokens : M → Set K

/-- The trivial signature structure (no tokens): the unauthenticated model. -/
def Auth.none (P M : Type*) : Auth P M Empty where
  signer := Empty.elim
  tokens _ := ∅

namespace Run

variable (Au : Auth P M K) (A : Algorithm P M S VI VO) (R : Run P M VI)

/-- Tokens received by `p` before time `τ`. -/
def recvTokens (p : P) (τ : ℕ) : Set K :=
  {x | ∃ τ' < τ, ∃ q, ∃ m ∈ R.inbox A p τ' q, x ∈ Au.tokens m}

/-- Tokens emitted by correct processes at times `≤ τ`. -/
def honestTokens (τ : ℕ) : Set K :=
  {x | ∃ τ' ≤ τ, ∃ q ∉ R.faulty, ∃ r, ∃ m ∈ R.out A q τ' r, x ∈ Au.tokens m}

/-- The adversary of `R` respects unforgeability. -/
def AuthValid : Prop :=
  ∀ b ∈ R.faulty, ∀ τ, ∀ r ∉ R.faulty, ∀ m ∈ R.byz b τ r, ∀ x ∈ Au.tokens m,
    Au.signer x ∈ R.faulty ∨ x ∈ R.honestTokens Au A τ

variable {Au A R}

theorem honestTokens_mono {τ τ' : ℕ} (h : τ ≤ τ') :
    R.honestTokens Au A τ ⊆ R.honestTokens Au A τ' := by
  rintro x ⟨σ, hσ, rest⟩; exact ⟨σ, hσ.trans h, rest⟩

theorem mem_inbox {p : P} {τ : ℕ} {q : P} {m : M} :
    m ∈ R.inbox A p τ q ↔ ∃ σ ≤ τ, R.dl q σ p = τ ∧ m ∈ R.out A q σ p := by
  rw [inbox_eq_flatMap, List.mem_flatMap]
  constructor
  · rintro ⟨σ, hσ, hm⟩
    simp only [dlv] at hm
    split_ifs at hm with h
    · exact ⟨σ, by simp at hσ; omega, h, hm⟩
    · simp at hm
  · rintro ⟨σ, hσ, h, hm⟩
    exact ⟨σ, by simp; omega, by simp [dlv, h, hm]⟩

/-- A run in which faulty processes are silent respects unforgeability. -/
theorem authValid_of_canonical (h : R.Canonical) : R.AuthValid Au A := by
  intro b hb τ r _ m hm
  simp [h b hb τ r] at hm

end Run

/-- Correct processes only emit their own tokens and tokens they have received. -/
def Algorithm.Unforging (A : Algorithm P M S VI VO) (Au : Auth P M K) : Prop :=
  ∀ (R : Run P M VI) p τ q, ∀ m ∈ A.send p (R.st A τ p) q, ∀ x ∈ Au.tokens m,
    Au.signer x = p ∨ x ∈ R.recvTokens Au A p τ

theorem Algorithm.unforging_none (A : Algorithm P M S VI VO) : A.Unforging (Auth.none P M) := by
  intro _ _ _ _ _ _ x; exact x.elim

theorem Run.authValid_none (A : Algorithm P M S VI VO) (R : Run P M VI) :
    R.AuthValid (Auth.none P M) A := by
  intro _ _ _ _ _ _ _ x; exact x.elim

namespace Run

variable {Au : Auth P M K} {A : Algorithm P M S VI VO}

/-- **Replay lemma.** Tokens occurring in messages of a reference run `Ri` up to time `T` are
signed by `R'`-Byzantine processes or emitted by `R'`-correct processes (by the same time),
provided every sender either (a) is correct in `R'` and sends the same as in `Ri`, or (b) is
Byzantine in `R'` and correct (i.e. running the algorithm) in `Ri`, or (c) only emits tokens of
`R'`-Byzantine signers in `Ri`. -/
theorem tokens_replay (hU : A.Unforging Au) {Ri R' : Run P M VI} {T : ℕ}
    (h : ∀ q σ r, σ ≤ T →
      (q ∉ R'.faulty ∧ R'.out A q σ r = Ri.out A q σ r) ∨ (q ∈ R'.faulty ∧ q ∉ Ri.faulty) ∨
      (∀ m ∈ Ri.out A q σ r, ∀ x ∈ Au.tokens m, Au.signer x ∈ R'.faulty)) :
    ∀ σ ≤ T, ∀ q r, ∀ m ∈ Ri.out A q σ r, ∀ x ∈ Au.tokens m,
      Au.signer x ∈ R'.faulty ∨ x ∈ R'.honestTokens Au A σ := by
  intro σ
  induction σ using Nat.strong_induction_on with
  | _ σ ih =>
    intro hσ q r m hm x hx
    rcases h q σ r hσ with ⟨hq, he⟩ | ⟨hq, hq'⟩ | hc
    · exact Or.inr ⟨σ, le_rfl, q, hq, r, m, he ▸ hm, hx⟩
    · rw [out_of_correct A Ri hq'] at hm
      rcases hU Ri q σ r m hm x hx with hs | ⟨τ', hτ', q', m', hm', hx'⟩
      · exact Or.inl (hs ▸ hq)
      · obtain ⟨σ', hσ', -, hm''⟩ := mem_inbox.mp hm'
        rcases ih σ' (by omega) (by omega) q' q m' hm'' x hx' with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (honestTokens_mono (by omega) h1)
    · exact Or.inl (hc m hm x hx)

end Run

/-- In isolation, a process only ever emits its own tokens. -/
theorem isoRun_tokens [Fintype P] {Au : Auth P M K} {A : Algorithm P M S VI VO}
    (hU : A.Unforging Au) (Q : P) (v : VI) :
    ∀ σ r, ∀ m ∈ A.send Q ((isoRun (M := M) Q v).st A σ Q) r, ∀ x ∈ Au.tokens m,
      Au.signer x = Q := by
  intro σ
  induction σ using Nat.strong_induction_on with
  | _ σ ih =>
    intro r m hm x hx
    rcases hU _ Q σ r m hm x hx with hs | ⟨τ', hτ', q, m', hm', hx'⟩
    · exact hs
    · obtain ⟨σ', hσ', -, hm''⟩ := Run.mem_inbox.mp hm'
      by_cases hq : q = Q
      · subst hq
        rw [Run.out_of_correct A _ (isoRun_correct q v)] at hm''
        exact ih σ' (by omega) q m' hm'' x hx'
      · rw [Run.out_eq_nil_of_canonical A (isoRun_canonical Q v)
          (by simp [isoRun, hq])] at hm''
        simp at hm''

/-- The canonical run respects unforgeability. -/
theorem canonRun_authValid [Fintype P] {Au : Auth P M K} {A : Algorithm P M S VI VO}
    (c : Config P VI) (d : VI) : (canonRun (M := M) c d).AuthValid Au A :=
  Run.authValid_of_canonical (canonRun.canonical c d)

/-- The extension of a canonical run respects unforgeability: the Byzantine processes only replay
messages of the canonical run up to `T`. -/
theorem Run.extend_authValid [Fintype P] {Au : Auth P M K} {A : Algorithm P M S VI VO}
    (hU : A.Unforging Au) {R : Run P M VI} (hcan : R.Canonical) {c' : Config P VI}
    (hsim : ∀ p ∉ R.faulty, c' p ≠ none → c' p = some (R.inp p)) (T : ℕ) :
    (R.extend A c' T).AuthValid Au A := by
  intro b _ τ r _ m hm x hx
  simp only [extend] at hm
  split_ifs at hm with hτ
  swap; · simp at hm
  refine tokens_replay hU (Ri := R) (T := T) (fun q σ r' hσ => ?_) τ hτ b r m hm x hx
  by_cases hq : q ∈ R.faulty
  · right; right
    intro m' hm'
    simp [out_eq_nil_of_canonical A hcan hq] at hm'
  · by_cases hq' : c' q = none
    · right; left
      exact ⟨by simp [extend, hq'], hq⟩
    · left
      have hq'' : q ∉ (R.extend A c' T).faulty := by
        simp [extend, Option.isSome_iff_ne_none, hq']
      refine ⟨hq'', ?_⟩
      rw [out_of_correct A _ hq'', out_of_correct A _ hq, extend_st hcan hsim T σ hσ q hq hq']

/-- `A` solves Byzantine consensus with `val` in the authenticated model `Au`: the requirements
hold in every valid run whose adversary respects unforgeability. -/
structure SolvesConsensusAuth [Fintype P] (Au : Auth P M K) (t δ : ℕ)
    (A : Algorithm P M S VI VO) (val : ValidityProperty P VI VO) : Prop where
  termination : ∀ R : Run P M VI, R.Valid t δ → R.AuthValid Au A →
    ∀ p ∉ R.faulty, ∃ v, R.Decides A p v
  agreement : ∀ R : Run P M VI, R.Valid t δ → R.AuthValid Au A →
    ∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w, R.Decides A p v → R.Decides A q w → v = w
  validity : ∀ R : Run P M VI, R.Valid t δ → R.AuthValid Au A →
    ∀ p ∉ R.faulty, ∀ v, R.Decides A p v → v ∈ val R.inputConf

theorem SolvesConsensus.auth [Fintype P] {t δ : ℕ} {A : Algorithm P M S VI VO}
    {val : ValidityProperty P VI VO} (h : SolvesConsensus t δ A val) (Au : Auth P M K) :
    SolvesConsensusAuth Au t δ A val :=
  ⟨fun R hR _ => h.termination R hR, fun R hR _ => h.agreement R hR,
    fun R hR _ => h.validity R hR⟩

theorem SolvesConsensusAuth.of_none [Fintype P] {t δ : ℕ} {A : Algorithm P M S VI VO}
    {val : ValidityProperty P VI VO} (h : SolvesConsensusAuth (Auth.none P M) t δ A val) :
    SolvesConsensus t δ A val :=
  ⟨fun R hR => h.termination R hR (R.authValid_none A),
    fun R hR => h.agreement R hR (R.authValid_none A),
    fun R hR => h.validity R hR (R.authValid_none A)⟩

/-- Solvability in the authenticated model: some unforging algorithm (with some message, state
and token types) solves consensus with `val`. -/
def ValidityProperty.SolvableAuth [Fintype P] (t δ : ℕ) (val : ValidityProperty P VI VO) :
    Prop :=
  ∃ (M S K : Type) (Au : Auth P M K) (A : Algorithm P M S VI VO),
    A.Unforging Au ∧ SolvesConsensusAuth Au t δ A val

/-- Unauthenticated solvability implies authenticated solvability. -/
theorem ValidityProperty.Solvable.solvableAuth [Fintype P] {t δ : ℕ}
    {val : ValidityProperty P VI VO} (h : val.Solvable t δ) : val.SolvableAuth t δ := by
  obtain ⟨M, S, A, hA⟩ := h
  exact ⟨M, S, Empty, Auth.none P M, A, A.unforging_none, hA.auth _⟩

end Cslib.Byzantine.PartialSync
