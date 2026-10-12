/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Auth

/-!
# Synchronous specifications on top of the partially synchronous model

The *synchronous* model is the special case `gst = 0` of the partially synchronous model
(`Cslib.Byzantine.PartialSync.Model`): every message between correct processes sent at time `τ` is
delivered in `[τ, τ + δ]`; for `δ = 0` this is exactly the lock-step round model (a message sent
at time `τ` is processed in the step at `τ`). An algorithm *solves consensus in synchrony* if the
requirements hold in every valid run with `gst = 0`; this is weaker than solving it in partial
synchrony (`SolvesConsensusAuth.sync`), so impossibility results / lower bounds for synchronous
solvers are stronger.

* `SolvesConsensusAuthSync Au t δ A val`, `SolvesConsensusSync` (`Au = Auth.none`).
* `ValidityProperty.SolvableSync`, `ValidityProperty.SolvableAuthSync`.
* `Contains c₁ c₂` (`c₁ ⊒ c₂`, containment of input configurations), `weakValidity`.
* `Run.enlarge R F'`: the run `R` in which the processes of `F' ⊇ R.faulty` are Byzantine and
  *replay* what they sent in `R`; it sends exactly the same messages (`enlarge_out`), correct
  processes cannot tell the difference (`enlarge_st`), and it respects unforgeability if `R`
  does (`enlarge_authValid`). This is the "same execution, fewer correct processes" construction
  (e.g. Lemma 7 of [CivitEtAl2024]).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P]

/-- `A` solves Byzantine consensus with `val` **in synchrony** (runs with `gst = 0`), in the
authenticated model `Au`. -/
structure SolvesConsensusAuthSync (Au : Auth P M K) (t δ : ℕ) (A : Algorithm P M S VI VO)
    (val : ValidityProperty P VI VO) : Prop where
  termination : ∀ R : Run P M VI, R.Valid t δ → R.AuthValid Au A → R.gst = 0 →
    ∀ p ∉ R.faulty, ∃ v, R.Decides A p v
  agreement : ∀ R : Run P M VI, R.Valid t δ → R.AuthValid Au A → R.gst = 0 →
    ∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w, R.Decides A p v → R.Decides A q w → v = w
  validity : ∀ R : Run P M VI, R.Valid t δ → R.AuthValid Au A → R.gst = 0 →
    ∀ p ∉ R.faulty, ∀ v, R.Decides A p v → v ∈ val R.inputConf

/-- `A` solves Byzantine consensus with `val` in synchrony, unauthenticated model. -/
abbrev SolvesConsensusSync (t δ : ℕ) (A : Algorithm P M S VI VO)
    (val : ValidityProperty P VI VO) : Prop :=
  SolvesConsensusAuthSync (Auth.none P M) t δ A val

variable {t δ : ℕ} {A : Algorithm P M S VI VO} {val : ValidityProperty P VI VO}
  {Au : Auth P M K}

/-- A partially synchronous solution is a synchronous solution. -/
theorem SolvesConsensusAuth.sync (h : SolvesConsensusAuth Au t δ A val) :
    SolvesConsensusAuthSync Au t δ A val :=
  ⟨fun R hR ha _ => h.termination R hR ha, fun R hR ha _ => h.agreement R hR ha,
    fun R hR ha _ => h.validity R hR ha⟩

set_option linter.unusedFintypeInType false in
/-- A partially synchronous solution is a synchronous solution. -/
theorem SolvesConsensus.sync (h : SolvesConsensus t δ A val) : SolvesConsensusSync t δ A val :=
  (h.auth _).sync

omit [Fintype P] in
/-- An unauthenticated synchronous solution works in every authenticated model. -/
theorem SolvesConsensusSync.auth (h : SolvesConsensusSync t δ A val) (Au : Auth P M K) :
    SolvesConsensusAuthSync Au t δ A val :=
  ⟨fun R hR _ h0 => h.termination R hR (R.authValid_none A) h0,
    fun R hR _ h0 => h.agreement R hR (R.authValid_none A) h0,
    fun R hR _ h0 => h.validity R hR (R.authValid_none A) h0⟩

omit [DecidableEq P] [Fintype P] in
theorem Run.Valid.mono_delta {R : Run P M VI} {δ' : ℕ} (h : R.Valid t δ') (hδ : δ' ≤ δ) :
    R.Valid t δ :=
  ⟨h.card_faulty, h.dl_ge, fun q τ p hq hp => (h.dl_le q τ p hq hp).trans (by omega)⟩

omit [Fintype P] in
/-- A synchronous solution for delay bound `δ` is one for every smaller delay bound. -/
theorem SolvesConsensusAuthSync.mono_delta {δ' : ℕ} (h : SolvesConsensusAuthSync Au t δ A val)
    (hδ : δ' ≤ δ) : SolvesConsensusAuthSync Au t δ' A val :=
  ⟨fun R hR => h.termination R (hR.mono_delta hδ), fun R hR => h.agreement R (hR.mono_delta hδ),
    fun R hR => h.validity R (hR.mono_delta hδ)⟩

/-- Synchronous solvability (unauthenticated): some algorithm (with message and state types in
`Type`) solves consensus with `val` in synchrony. -/
def ValidityProperty.SolvableSync (t δ : ℕ) (val : ValidityProperty P VI VO) : Prop :=
  ∃ (M S : Type) (A : Algorithm P M S VI VO), SolvesConsensusSync t δ A val

/-- Synchronous solvability with ideal signatures. -/
def ValidityProperty.SolvableAuthSync (t δ : ℕ) (val : ValidityProperty P VI VO) : Prop :=
  ∃ (M S K : Type) (Au : Auth P M K) (A : Algorithm P M S VI VO),
    A.Unforging Au ∧ SolvesConsensusAuthSync Au t δ A val

omit [Fintype P] in
theorem ValidityProperty.SolvableSync.solvableAuthSync (h : val.SolvableSync t δ) :
    val.SolvableAuthSync t δ := by
  obtain ⟨M, S, A, hA⟩ := h
  exact ⟨M, S, Empty, Auth.none P M, A, A.unforging_none, hA⟩

set_option linter.unusedFintypeInType false in
theorem ValidityProperty.Solvable.solvableSync (h : val.Solvable t δ) : val.SolvableSync t δ := by
  obtain ⟨M, S, A, hA⟩ := h
  exact ⟨M, S, A, hA.sync⟩

theorem ValidityProperty.SolvableAuth.solvableAuthSync (h : val.SolvableAuth t δ) :
    val.SolvableAuthSync t δ := by
  obtain ⟨M, S, K, Au, A, hU, hA⟩ := h
  exact ⟨M, S, K, Au, A, hU, hA.sync⟩

omit [Fintype P] in
theorem ValidityProperty.SolvableSync.mono_delta {δ' : ℕ} (h : val.SolvableSync t δ)
    (hδ : δ' ≤ δ) : val.SolvableSync t δ' := by
  obtain ⟨M, S, A, hA⟩ := h
  exact ⟨M, S, A, hA.mono_delta hδ⟩

omit [Fintype P] in
theorem ValidityProperty.SolvableAuthSync.mono_delta {δ' : ℕ} (h : val.SolvableAuthSync t δ)
    (hδ : δ' ≤ δ) : val.SolvableAuthSync t δ' := by
  obtain ⟨M, S, K, Au, A, hU, hA⟩ := h
  exact ⟨M, S, K, Au, A, hU, hA.mono_delta hδ⟩

/-- **Containment** `c₁ ⊒ c₂`: every process of `π(c₂)` belongs to `π(c₁)` with the same
proposal. -/
def Contains (c₁ c₂ : Config P VI) : Prop := ∀ p, c₂ p ≠ none → c₁ p = c₂ p

omit [Fintype P] [DecidableEq P] in
theorem Contains.refl (c : Config P VI) : Contains c c := fun _ _ => rfl

omit [Fintype P] [DecidableEq P] in
theorem Contains.trans {c₁ c₂ c₃ : Config P VI} (h₁ : Contains c₁ c₂) (h₂ : Contains c₂ c₃) :
    Contains c₁ c₃ := fun p hp => (h₁ p (by rwa [h₂ p hp])).trans (h₂ p hp)

omit [DecidableEq P] in
theorem Contains.procs_subset {c₁ c₂ : Config P VI} (h : Contains c₁ c₂) :
    c₂.procs ⊆ c₁.procs := by
  intro p hp
  rw [Config.mem_procs_iff_ne_none] at hp ⊢
  rw [h p hp]; exact hp

/-- **Weak validity**: if all processes are correct and propose the same value `v`, then `v` is
the only admissible decision; otherwise every decision is admissible. -/
def weakValidity (P V : Type*) : ValidityProperty P V V :=
  fun c => {w | ∀ v, (∀ p, c p = some v) → w = v}

/-- **IC-Validity**: the decided vector `V` contains the input configuration, i.e. `V[i]` is the
proposal of every correct process `p_i` (`IC-Validity(c) = {V ∈ I_n | V ⊒ c}`). -/
def icValidity (P VI : Type*) : ValidityProperty P VI (P → VI) :=
  fun c => {V | ∀ p, c p ≠ none → c p = some (V p)}

omit [Fintype P] [DecidableEq P] in
theorem mem_icValidity_iff {c : Config P VI} {V : P → VI} :
    V ∈ icValidity P VI c ↔ Contains (fun p => some (V p)) c := by
  simp only [icValidity, Set.mem_ofPred_eq, Contains]
  exact forall_congr' fun p => imp_congr_right fun _ => eq_comm

namespace Run

omit [Fintype P] in
/-- In a run with zero delays, `p` receives at time `τ` exactly what is sent to it at time `τ`. -/
theorem inbox_of_dl_eq (A : Algorithm P M S VI VO)
    {R : Run P M VI} (h : ∀ q τ p, R.dl q τ p = τ) (p : P) (τ : ℕ) (q : P) :
    R.inbox A p τ q = R.out A q τ p := by
  rw [Run.inbox_eq_flatMap, List.range_succ, List.flatMap_append]
  simp only [Run.dlv, h]
  simp only [List.flatMap_cons, List.flatMap_nil, ite_true, List.append_nil,
    List.append_left_eq_self,
    List.flatMap_eq_nil_iff, List.mem_range]
  intro x hx
  simp [show x ≠ τ by omega]

variable (A) (R : Run P M VI)

/-- The run `R` in which the processes of `F'` are Byzantine and replay what they sent in `R`. -/
def enlarge (F' : Finset P) : Run P M VI :=
  { R with faulty := F', byz := R.out A }

variable {A R}

omit [Fintype P] in
@[simp] theorem enlarge_faulty (F' : Finset P) : (R.enlarge A F').faulty = F' := rfl
omit [Fintype P] in
@[simp] theorem enlarge_gst (F' : Finset P) : (R.enlarge A F').gst = R.gst := rfl
omit [Fintype P] in
@[simp] theorem enlarge_inp (F' : Finset P) : (R.enlarge A F').inp = R.inp := rfl
omit [Fintype P] in
@[simp] theorem enlarge_dl (F' : Finset P) : (R.enlarge A F').dl = R.dl := rfl

omit [Fintype P] in
/-- Processes correct in `R.enlarge A F'` have the same states as in `R`. -/
theorem enlarge_st {F' : Finset P} (hF : R.faulty ⊆ F') :
    ∀ τ, ∀ p ∉ F', (R.enlarge A F').st A τ p = R.st A τ p := by
  intro τ p hp
  refine (R.enlarge A F').st_eq_of_inbox_eq A (ref := fun _ => R) (X := {p | p ∉ F'})
    (fun _ _ => rfl) (fun σ _ ih r hr => ?_) τ le_rfl p hp
  refine (R.enlarge A F').inbox_eq_of_dlv_eq A fun q σ' hσ' => ?_
  simp only [dlv, enlarge_dl]
  by_cases hd : R.dl q σ' r = σ
  · simp only [hd, ite_true]
    by_cases hq : q ∈ F'
    · rw [out_of_faulty A _ (by simpa using hq)]; rfl
    · rw [out_of_correct A _ (by simpa using hq), out_of_correct A _ (fun h => hq (hF h)),
        ih q hq σ' hσ']
  · simp [hd]

omit [Fintype P] in
/-- `R.enlarge A F'` sends exactly the messages of `R`. -/
theorem enlarge_out {F' : Finset P} (hF : R.faulty ⊆ F') : (R.enlarge A F').out A = R.out A := by
  funext q τ p
  by_cases hq : q ∈ F'
  · rw [out_of_faulty A _ (by simpa using hq)]; rfl
  · rw [out_of_correct A _ (by simpa using hq), out_of_correct A _ (fun h => hq (hF h)),
      enlarge_st hF τ q hq]

omit [Fintype P] in
theorem enlarge_inbox {F' : Finset P} (hF : R.faulty ⊆ F') :
    (R.enlarge A F').inbox A = R.inbox A := by
  funext p τ q
  rw [inbox_eq_flatMap, inbox_eq_flatMap]
  simp [dlv, enlarge_out hF]

omit [Fintype P] in
theorem enlarge_valid {F' : Finset P} (hR : R.Valid t δ) (hF : R.faulty ⊆ F')
    (hcard : F'.card ≤ t) : (R.enlarge A F').Valid t δ where
  card_faulty := hcard
  dl_ge q τ p hq hp := hR.dl_ge q τ p (fun h => hq (hF h)) (fun h => hp (hF h))
  dl_le q τ p hq hp := hR.dl_le q τ p (fun h => hq (hF h)) (fun h => hp (hF h))

omit [Fintype P] in
theorem enlarge_decides {F' : Finset P} (hF : R.faulty ⊆ F') {p : P} (hp : p ∉ F') {v : VO} :
    (R.enlarge A F').Decides A p v ↔ R.Decides A p v := by
  simp only [Decides, enlarge_st hF _ p hp]

omit [Fintype P] in
/-- **Replaying a run with more Byzantine processes respects unforgeability.** If `A` is unforging
and `R` respects unforgeability, so does `R.enlarge A F'` for `F' ⊇ R.faulty`. -/
theorem enlarge_authValid {F' : Finset P} (hU : A.Unforging Au) (hRa : R.AuthValid Au A)
    (hF : R.faulty ⊆ F') : (R.enlarge A F').AuthValid Au A := by
  set R' := R.enlarge A F'
  have hout := enlarge_out (A := A) (R := R) hF
  -- tokens of messages sent by `R`-correct processes up to `σ`
  have key : ∀ σ, (∀ σ' < σ, ∀ q r, (q ∉ R.faulty ∨ r ∉ R.faulty) → ∀ m ∈ R.out A q σ' r,
      ∀ x ∈ Au.tokens m, Au.signer x ∈ F' ∨ x ∈ R'.honestTokens Au A σ') →
      ∀ q ∉ R.faulty, ∀ r, ∀ m ∈ R.out A q σ r, ∀ x ∈ Au.tokens m,
        Au.signer x ∈ F' ∨ x ∈ R'.honestTokens Au A σ := by
    intro σ ih q hq r m hm x hx
    by_cases hq' : q ∈ F'
    · rw [out_of_correct A R hq] at hm
      rcases hU R q σ r m hm x hx with hs | ⟨τ', hτ', q', m', hm', hx'⟩
      · exact Or.inl (hs ▸ hq')
      · obtain ⟨σ', hσ', -, hm''⟩ := mem_inbox.mp hm'
        rcases ih σ' (by omega) q' q (Or.inr hq) m' hm'' x hx' with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (honestTokens_mono (by omega) h1)
    · exact Or.inr ⟨σ, le_rfl, q, by simpa [R'] using hq', r, m, by rw [hout]; exact hm, hx⟩
  have main : ∀ σ, ∀ q r, (q ∉ R.faulty ∨ r ∉ R.faulty) → ∀ m ∈ R.out A q σ r,
      ∀ x ∈ Au.tokens m, Au.signer x ∈ F' ∨ x ∈ R'.honestTokens Au A σ := by
    intro σ
    induction σ using Nat.strong_induction_on with
    | _ σ ih =>
      intro q r hqr m hm x hx
      by_cases hq : q ∈ R.faulty
      · have hr : r ∉ R.faulty := hqr.resolve_left (not_not.mpr hq)
        rw [out_of_faulty A R hq] at hm
        rcases hRa q hq σ r hr m hm x hx with hs | ⟨σ'', hσ'', q'', hq'', r'', m'', hm'', hx''⟩
        · exact Or.inl (hF hs)
        · rcases key σ'' (fun σ' h => ih σ' (by omega)) q'' hq'' r'' m'' hm'' x hx'' with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (honestTokens_mono hσ'' h1)
      · exact key σ ih q hq r m hm x hx
  intro b hb τ r hr m hm x hx
  have hr' : r ∉ R.faulty := fun h => hr (hF h)
  exact main τ b r (Or.inr hr') m hm x hx

omit [Fintype P] in
/-- The input configuration of the enlarged run: the processes of `F'` are removed. -/
theorem enlarge_inputConf (F' : Finset P) (p : P) :
    (R.enlarge A F').inputConf p = if p ∈ F' then none else some (R.inp p) := rfl

end Run

end Cslib.Byzantine.PartialSync
