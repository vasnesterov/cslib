/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.LockStep.Parallel

/-!
# Sequential composition and input/output wrapping of lock-step protocols

Complements CSLib's `Cslib.Byzantine.LockStep` (which has parallel composition, `comapInput`,
`mapOutput`) with the two operations needed to state *reductions* between synchronous
problems ("run `A` for `R` rounds, then run `B` on an input computed from `A`'s output"):

* `Protocol.seq A R f B`: run `A` during rounds `0, …, R-1`; at round `R` every party computes
  the input `f p x o` of `B` from its own input `x` and its first decision `o : Option O₁` of `A`
  within the first `R` rounds (`none` if `A` has not decided), and then runs `B`. Messages are
  `M₁ ⊕ M₂`. All parties start `B` simultaneously, as in the "wait until round `R` ends" step of
  synchronous protocol compositions.
* `Protocol.wrap alg fi fo`: run `alg` on the translated input `fi p x` and output
  `fo p x o` (the post-processing may depend on the original input, unlike `mapOutput`).

Main facts: the projection lemmas `histL_hist_seq` / `histR_hist_seq` identify the two phases of a
run of `seq` with a run of `A` in `s.seqFst R` and a run of `B` in `s.seqSnd R …`;
`decides_seq_iff`, `seqInputs_eq_firstUpTo`, `seqInputs_eq` and `terminatesBy_seq` transfer
decisions/termination;
`Scenario.AuthValid.seqFst/seqSnd` and `Protocol.Unforging.seq` transfer the authenticated
setting (tokens `S₁ ⊕ S₂`). For an arbitrary signature structure `Aut` on `M₁ ⊕ M₂` (one token
type for both phases), `Protocol.Unforging.seq_of_left_right` and `Scenario.AuthValid.seqFst_left`
do the same with the left / right parts `Aut.left`, `Aut.right` (`Cslib.Byzantine.Auth.left`,
`Cslib.Byzantine.Auth.right`).

`SolvesAuthWithin` packages "solves `spec` within `T` rounds against `Z` in the authenticated
setting, for runs whose inputs satisfy `pre`" (the unauthenticated setting is `Auth.none`).
-/

@[expose] public section

namespace Cslib.Byzantine.LockStep

variable {P I M M₁ M₂ O O₁ I₂ S S₁ S₂ : Type*}

/-! ### Solving a problem within a round bound -/

/-- `alg` solves `spec` against the adversary structure `Z` on network `G`, in the authenticated
setting `A`, and all honest parties decide within `T` rounds — for every run whose inputs satisfy
the precondition `pre` (e.g. "the honest inputs are `D`-close"). -/
def SolvesAuthWithin (G : SimpleGraph P) (alg : Protocol P I M O) (A : Auth P M S)
    (Z : AdvStructure P) (pre : (P → I) → Set P → Prop) (spec : Spec P I O) (T : ℕ) : Prop :=
  ∀ s : Scenario P I M, s.byz ∈ Z → s.Reliable → s.AuthValid G alg A → pre s.input s.honest →
    spec s.input s.honest (Decides G alg s) ∧ TerminatesBy G alg s T

/-- The trivial precondition. -/
def noPre : (P → I) → Set P → Prop := fun _ _ => True

/-! ### Termination of parallel compositions -/

lemma terminatesBy_parallel {ι : Type*} {Mi : ι → Type*} (G : SimpleGraph P)
    (algs : (i : ι) → Protocol P I (Mi i) O) (s : Scenario P I ((j : ι) → Option (Mi j))) (T : ℕ)
    (h : ∀ i, TerminatesBy G (algs i) (s.proj i) T) :
    TerminatesBy G (Protocol.parallel algs) s T := by
  intro p hp
  refine ⟨T, le_rfl, ?_⟩
  rw [status_parallel]
  have : ∀ i, ∃ o, firstUpTo (fun j => status G (algs i) (s.proj i) j p) T = some o := by
    intro i
    obtain ⟨r, hr, o, ho⟩ := h i p hp
    rcases hfu : firstUpTo (fun j => status G (algs i) (s.proj i) j p) T with _ | o'
    · exact absurd ho (by rw [firstUpTo_eq_none.1 hfu r hr]; simp)
    · exact ⟨o', rfl⟩
  choose d hd using this
  exact ⟨d, allSome_eq_some.2 hd⟩

/-! ### Wrapping: translate inputs, post-process outputs -/

section Wrap

variable {I' O' : Type*}

/-- Run `alg` on input `fi p x` and output `fo p x o` when `alg` decides `o`. -/
def Protocol.wrap (alg : Protocol P I M O) (fi : P → I' → I) (fo : P → I' → O → O') :
    Protocol P I' M O' where
  send p x h q := alg.send p (fi p x) h q
  decide p x h := (alg.decide p (fi p x) h).map (fo p x)

/-- The scenario with translated inputs. -/
def Scenario.wrapIn (s : Scenario P I' M) (fi : P → I' → I) : Scenario P I M :=
  { s with input := fun p => fi p (s.input p) }

variable (G : SimpleGraph P) (alg : Protocol P I M O) (fi : P → I' → I) (fo : P → I' → O → O')

lemma hist_wrap (s : Scenario P I' M) : hist G (alg.wrap fi fo) s = hist G alg (s.wrapIn fi) := by
  funext r
  induction r with
  | zero => rfl
  | succ r ih =>
    funext q
    rw [hist_succ, hist_succ, ih]
    rfl

lemma status_wrap (s : Scenario P I' M) (r : ℕ) (p : P) :
    status G (alg.wrap fi fo) s r p = (status G alg (s.wrapIn fi) r p).map (fo p (s.input p)) := by
  simp only [status, hist_wrap]
  rfl

lemma decides_wrap_iff (s : Scenario P I' M) (p : P) (o' : O') :
    Decides G (alg.wrap fi fo) s p o' ↔
      ∃ o, Decides G alg (s.wrapIn fi) p o ∧ fo p (s.input p) o = o' := by
  simp only [Decides, status_wrap]
  constructor
  · rintro ⟨r, hr, hmin⟩
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hr
    exact ⟨o, ⟨r, ho, fun r' hr' => Option.map_eq_none_iff.1 (hmin r' hr')⟩, rfl⟩
  · rintro ⟨o, ⟨r, ho, hmin⟩, rfl⟩
    exact ⟨r, by simp [ho], fun r' hr' => by simp [hmin r' hr']⟩

lemma terminatesBy_wrap (s : Scenario P I' M) (T : ℕ)
    (h : TerminatesBy G alg (s.wrapIn fi) T) : TerminatesBy G (alg.wrap fi fo) s T := by
  intro p hp
  obtain ⟨r, hr, o, ho⟩ := h p hp
  exact ⟨r, hr, fo p (s.input p) o, by rw [status_wrap, ho]; rfl⟩

lemma Protocol.Unforging.wrap {A : Auth P M S} (hU : alg.Unforging A) :
    (alg.wrap fi fo).Unforging A := fun p x h q m hm => hU p (fi p x) h q m hm

lemma Scenario.authValid_wrap (A : Auth P M S) (s : Scenario P I' M) :
    s.AuthValid G (alg.wrap fi fo) A ↔ (s.wrapIn fi).AuthValid G alg A := by
  simp only [Scenario.AuthValid, honestTokens, hist_wrap]
  rfl

@[simp] lemma Scenario.wrapIn_byz (s : Scenario P I' M) : (s.wrapIn fi).byz = s.byz := rfl
@[simp] lemma Scenario.wrapIn_input (s : Scenario P I' M) (p : P) :
    (s.wrapIn fi).input p = fi p (s.input p) := rfl
@[simp] lemma Scenario.wrapIn_honest (s : Scenario P I' M) : (s.wrapIn fi).honest = s.honest := rfl
lemma Scenario.Reliable.wrapIn {s : Scenario P I' M} (h : s.Reliable) : (s.wrapIn fi).Reliable := h

end Wrap

/-! ### Sequential composition -/

section Seq

/-- Left components of an inbox of sum messages. -/
def inboxL (ib : Inbox P (M₁ ⊕ M₂)) : Inbox P M₁ := fun q => (ib q).bind Sum.getLeft?

/-- Right components of an inbox of sum messages. -/
def inboxR (ib : Inbox P (M₁ ⊕ M₂)) : Inbox P M₂ := fun q => (ib q).bind Sum.getRight?

/-- Left components of a history. -/
def histL (h : History P (M₁ ⊕ M₂)) : History P M₁ := h.map inboxL

/-- Right components of a history. -/
def histR (h : History P (M₁ ⊕ M₂)) : History P M₂ := h.map inboxR

/-- The input of the second phase, computed from the history of the first `R` rounds. -/
def Protocol.seqInput (A : Protocol P I M₁ O₁) (R : ℕ) (f : P → I → Option O₁ → I₂) (p : P)
    (x : I) (h : History P (M₁ ⊕ M₂)) : I₂ :=
  f p x (A.firstDecide p x (histL (h.take R)))

/-- **Sequential composition**: run `A` for exactly `R` rounds, then run `B` on input
`f p x o`, where `o` is `p`'s first decision in `A` within the first `R` rounds. -/
def Protocol.seq (A : Protocol P I M₁ O₁) (R : ℕ) (f : P → I → Option O₁ → I₂)
    (B : Protocol P I₂ M₂ O) : Protocol P I (M₁ ⊕ M₂) O where
  send p x h q :=
    if h.length < R then (A.send p x (histL h) q).map Sum.inl
    else (B.send p (A.seqInput R f p x h) (histR (h.drop R)) q).map Sum.inr
  decide p x h :=
    if h.length < R then none else B.decide p (A.seqInput R f p x h) (histR (h.drop R))

/-- The scenario of the first phase (Byzantine messages after round `R` are irrelevant and
dropped). -/
def Scenario.seqFst (s : Scenario P I (M₁ ⊕ M₂)) (R : ℕ) : Scenario P I M₁ where
  byz := s.byz
  input := s.input
  adv r b q := if r < R then (s.adv r b q).bind Sum.getLeft? else none
  drop := s.drop

/-- The scenario of the second phase, with inputs `x₂`. -/
def Scenario.seqSnd (s : Scenario P I (M₁ ⊕ M₂)) (R : ℕ) (x₂ : P → I₂) : Scenario P I₂ M₂ where
  byz := s.byz
  input := x₂
  adv r b q := (s.adv (R + r) b q).bind Sum.getRight?
  drop r := s.drop (R + r)

section Simp
variable (s : Scenario P I (M₁ ⊕ M₂)) (R : ℕ) (x₂ : P → I₂)
@[simp] lemma Scenario.seqFst_byz : (s.seqFst R).byz = s.byz := rfl
@[simp] lemma Scenario.seqFst_input : (s.seqFst R).input = s.input := rfl
@[simp] lemma Scenario.seqFst_honest : (s.seqFst R).honest = s.honest := rfl
@[simp] lemma Scenario.seqSnd_byz : (s.seqSnd R x₂).byz = s.byz := rfl
@[simp] lemma Scenario.seqSnd_input : (s.seqSnd R x₂).input = x₂ := rfl
@[simp] lemma Scenario.seqSnd_honest : (s.seqSnd R x₂).honest = s.honest := rfl
lemma Scenario.Reliable.seqFst {s : Scenario P I (M₁ ⊕ M₂)} (h : s.Reliable) :
    (s.seqFst R).Reliable := h
lemma Scenario.Reliable.seqSnd {s : Scenario P I (M₁ ⊕ M₂)} (h : s.Reliable) :
    (s.seqSnd R x₂).Reliable := fun r => h (R + r)
end Simp

@[simp] lemma histL_append (h₁ h₂ : History P (M₁ ⊕ M₂)) :
    histL (h₁ ++ h₂) = histL h₁ ++ histL h₂ := List.map_append
@[simp] lemma histR_append (h₁ h₂ : History P (M₁ ⊕ M₂)) :
    histR (h₁ ++ h₂) = histR h₁ ++ histR h₂ := List.map_append

variable (G : SimpleGraph P) (A : Protocol P I M₁ O₁) (R : ℕ) (f : P → I → Option O₁ → I₂)
  (B : Protocol P I₂ M₂ O)

lemma seq_send_lt {p : P} {x : I} {h : History P (M₁ ⊕ M₂)} (hh : h.length < R) (q : P) :
    (A.seq R f B).send p x h q = (A.send p x (histL h) q).map Sum.inl := by
  simp [Protocol.seq, hh]

lemma seq_send_ge {p : P} {x : I} {h : History P (M₁ ⊕ M₂)} (hh : R ≤ h.length) (q : P) :
    (A.seq R f B).send p x h q =
      (B.send p (A.seqInput R f p x h) (histR (h.drop R)) q).map Sum.inr := by
  simp [Protocol.seq, not_lt.2 hh]

/-- **First projection lemma**: during the first `R` rounds, the left components of a run of
`seq` form the run of `A` in `s.seqFst R`. -/
lemma histL_hist_seq (s : Scenario P I (M₁ ⊕ M₂)) :
    ∀ r ≤ R, ∀ p, histL (hist G (A.seq R f B) s r p) = hist G A (s.seqFst R) r p := by
  intro r
  induction r with
  | zero => intro _ p; rfl
  | succ r ih =>
    intro hr p
    have hrR : r < R := hr
    rw [hist_succ, hist_succ, histL_append, ih hrR.le]
    congr 1
    simp only [histL, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    funext q
    simp only [inboxL, deliver]
    by_cases hadj : G.Adj q p
    · by_cases hb : q ∈ s.byz
      · simp [hadj, hb, Scenario.seqFst, hrR]
      · by_cases hd : s.drop r q p
        · simp [hadj, hb, hd, Scenario.seqFst]
        · have hlen : (hist G (A.seq R f B) s r q).length < R := by simpa using hrR
          have hd' : ¬ (s.seqFst R).drop r q p := hd
          simp only [hadj, hb, hd, hd', ite_true, ite_false, Scenario.seqFst_byz,
            Scenario.seqFst_input,
            seq_send_lt A R f B hlen, ih hrR.le q]
          cases A.send q (s.input q) (hist G A (s.seqFst R) r q) p <;> rfl
    · simp [hadj]

/-- The input with which `p` starts the second phase in the run `s`. -/
noncomputable def seqInputs (s : Scenario P I (M₁ ⊕ M₂)) (p : P) : I₂ :=
  f p (s.input p) (A.firstDecide p (s.input p) (hist G A (s.seqFst R) R p))

lemma seqInput_hist (s : Scenario P I (M₁ ⊕ M₂)) (r : ℕ) (p : P) :
    A.seqInput R f p (s.input p) (hist G (A.seq R f B) s (R + r) p) = seqInputs G A R f s p := by
  unfold Protocol.seqInput seqInputs
  rw [take_hist G _ s (Nat.le_add_right R r), histL_hist_seq G A R f B s R le_rfl]

/-- **Second projection lemma**: from round `R` on, the right components of a run of `seq`
form the run of `B` in `s.seqSnd R (seqInputs …)`. -/
lemma histR_hist_seq (s : Scenario P I (M₁ ⊕ M₂)) :
    ∀ r p, histR ((hist G (A.seq R f B) s (R + r) p).drop R) =
      hist G B (s.seqSnd R (seqInputs G A R f s)) r p := by
  intro r
  induction r with
  | zero => intro p; simp [histR]
  | succ r ih =>
    intro p
    rw [← Nat.add_assoc, hist_succ, hist_succ,
      List.drop_append_of_le_length (by simp), histR_append, ih]
    congr 1
    simp only [histR, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    funext q
    simp only [inboxR, deliver]
    by_cases hadj : G.Adj q p
    · by_cases hb : q ∈ s.byz
      · simp [hadj, hb, Scenario.seqSnd]
      · by_cases hd : s.drop (R + r) q p
        · simp [hadj, hb, hd, Scenario.seqSnd]
        · have hlen : R ≤ (hist G (A.seq R f B) s (R + r) q).length := by simp
          have hd' : ¬ (s.seqSnd R (seqInputs G A R f s)).drop r q p := hd
          simp only [hadj, hb, hd, hd', ite_true, ite_false, Scenario.seqSnd_byz,
            Scenario.seqSnd_input,
            seq_send_ge A R f B hlen, ih q, seqInput_hist G A R f B s r q]
          cases B.send q (seqInputs G A R f s q)
            (hist G B (s.seqSnd R (seqInputs G A R f s)) r q) p <;> rfl
    · simp [hadj]

lemma status_seq_lt (s : Scenario P I (M₁ ⊕ M₂)) {r : ℕ} (hr : r < R) (p : P) :
    status G (A.seq R f B) s r p = none := by
  simp [status, Protocol.seq, hr]

lemma status_seq_add (s : Scenario P I (M₁ ⊕ M₂)) (r : ℕ) (p : P) :
    status G (A.seq R f B) s (R + r) p =
      status G B (s.seqSnd R (seqInputs G A R f s)) r p := by
  have hlen : R ≤ (hist G (A.seq R f B) s (R + r) p).length := by simp
  have hdec : ∀ {x : I} {h : History P (M₁ ⊕ M₂)}, R ≤ h.length →
      (A.seq R f B).decide p x h = B.decide p (A.seqInput R f p x h) (histR (h.drop R)) := by
    intro x h hh; simp [Protocol.seq, not_lt.2 hh]
  unfold status
  rw [hdec hlen, seqInput_hist G A R f B s r p, histR_hist_seq G A R f B s r p]
  rfl

/-- **Decision correspondence** for the sequential composition. -/
theorem decides_seq_iff (s : Scenario P I (M₁ ⊕ M₂)) (p : P) (o : O) :
    Decides G (A.seq R f B) s p o ↔ Decides G B (s.seqSnd R (seqInputs G A R f s)) p o := by
  constructor
  · rintro ⟨r, hr, hmin⟩
    have hRr : R ≤ r := by
      by_contra h
      rw [status_seq_lt G A R f B s (not_le.1 h)] at hr
      exact absurd hr (by simp)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hRr
    refine ⟨k, by rwa [← status_seq_add], fun r' hr' => ?_⟩
    rw [← status_seq_add]
    exact hmin _ (by omega)
  · rintro ⟨k, hk, hmin⟩
    refine ⟨R + k, by rwa [status_seq_add], fun r' hr' => ?_⟩
    by_cases h : r' < R
    · exact status_seq_lt G A R f B s h p
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
      rw [status_seq_add]
      exact hmin j (by omega)

/-- The input of the second phase is computed from the first decision within `R` rounds. -/
lemma seqInputs_eq_firstUpTo (s : Scenario P I (M₁ ⊕ M₂)) (p : P) :
    seqInputs G A R f s p =
      f p (s.input p) (firstUpTo (fun j => status G A (s.seqFst R) j p) R) := by
  unfold seqInputs
  rw [Protocol.firstDecide, length_hist]
  exact congrArg _ (firstUpTo_congr fun j hj => by rw [take_hist G _ _ hj]; rfl)

/-- If `p` decides `o₁` in the first phase within `R` rounds, it starts the second phase with
input `f p x (some o₁)`. -/
lemma seqInputs_eq (s : Scenario P I (M₁ ⊕ M₂)) (p : P) (o₁ : O₁)
    (hd : Decides G A (s.seqFst R) p o₁) (hT : ∃ r ≤ R, ∃ o, status G A (s.seqFst R) r p = some o) :
    seqInputs G A R f s p = f p (s.input p) (some o₁) := by
  rw [seqInputs_eq_firstUpTo]
  obtain ⟨r₀, hr₀, hmin⟩ := hd
  have hr₀R : r₀ ≤ R := by
    obtain ⟨r, hr, o, ho⟩ := hT
    by_contra h
    have := hmin r (by omega)
    rw [ho] at this
    exact absurd this (by simp)
  rw [firstUpTo_of_firstSome hr₀ hmin hr₀R]

lemma terminatesBy_seq (s : Scenario P I (M₁ ⊕ M₂)) (T : ℕ)
    (h : TerminatesBy G B (s.seqSnd R (seqInputs G A R f s)) T) :
    TerminatesBy G (A.seq R f B) s (R + T) := by
  intro p hp
  obtain ⟨r, hr, o, ho⟩ := h p hp
  exact ⟨R + r, by omega, o, by rw [status_seq_add, ho]⟩

/-! #### Authenticated setting -/

/-- Signature structure of a sequential composition: tokens of the two phases are kept apart. -/
def Auth.seq (A₁ : Auth P M₁ S₁) (A₂ : Auth P M₂ S₂) : Auth P (M₁ ⊕ M₂) (S₁ ⊕ S₂) where
  signer := Sum.elim A₁.signer A₂.signer
  tokens := Sum.elim (fun m => Sum.inl '' A₁.tokens m) (fun m => Sum.inr '' A₂.tokens m)

variable {G A R f B}

lemma Auth.seq_histTokens_L (A₁ : Auth P M₁ S₁) (A₂ : Auth P M₂ S₂) (h : History P (M₁ ⊕ M₂))
    {τ : S₁} (hτ : τ ∈ A₁.histTokens (histL h)) : Sum.inl τ ∈ (Auth.seq A₁ A₂).histTokens h := by
  obtain ⟨ib, hib, q, m, hm, hτm⟩ := hτ
  obtain ⟨ib₀, hib₀, rfl⟩ := List.mem_map.1 hib
  obtain ⟨m₀, hm₀, hm₀l⟩ := Option.bind_eq_some_iff.1 hm
  cases m₀ with
  | inl m₁ =>
    simp only [Sum.getLeft?_inl, Option.some.injEq] at hm₀l
    subst hm₀l
    exact ⟨ib₀, hib₀, q, Sum.inl m₁, hm₀, ⟨τ, hτm, rfl⟩⟩
  | inr m₂ => simp at hm₀l

lemma Auth.seq_histTokens_R (A₁ : Auth P M₁ S₁) (A₂ : Auth P M₂ S₂) (h : History P (M₁ ⊕ M₂))
    {τ : S₂} (hτ : τ ∈ A₂.histTokens (histR (h.drop R))) :
    Sum.inr τ ∈ (Auth.seq A₁ A₂).histTokens h := by
  obtain ⟨ib, hib, q, m, hm, hτm⟩ := hτ
  obtain ⟨ib₀, hib₀, rfl⟩ := List.mem_map.1 hib
  obtain ⟨m₀, hm₀, hm₀r⟩ := Option.bind_eq_some_iff.1 hm
  cases m₀ with
  | inr m₂ =>
    simp only [Sum.getRight?_inr, Option.some.injEq] at hm₀r
    subst hm₀r
    exact ⟨ib₀, List.mem_of_mem_drop hib₀, q, Sum.inr m₂, hm₀, ⟨τ, hτm, rfl⟩⟩
  | inl m₁ => simp at hm₀r

lemma Protocol.Unforging.seq {A₁ : Auth P M₁ S₁} {A₂ : Auth P M₂ S₂} (hA : A.Unforging A₁)
    (hB : B.Unforging A₂) : (A.seq R f B).Unforging (Auth.seq A₁ A₂) := by
  intro p x h q m hm τ hτ
  simp only [Protocol.seq] at hm
  split_ifs at hm with hlt
  · obtain ⟨m₁, hm₁, rfl⟩ := Option.map_eq_some_iff.1 hm
    obtain ⟨τ₁, hτ₁, rfl⟩ := hτ
    rcases hA p x _ q m₁ hm₁ τ₁ hτ₁ with hs | hs
    · exact Or.inl hs
    · exact Or.inr (Auth.seq_histTokens_L A₁ A₂ h hs)
  · obtain ⟨m₂, hm₂, rfl⟩ := Option.map_eq_some_iff.1 hm
    obtain ⟨τ₂, hτ₂, rfl⟩ := hτ
    rcases hB p _ _ q m₂ hm₂ τ₂ hτ₂ with hs | hs
    · exact Or.inl hs
    · exact Or.inr (Auth.seq_histTokens_R A₁ A₂ h hs)

variable (G A R f B)

lemma Scenario.AuthValid.seqFst {A₁ : Auth P M₁ S₁} {A₂ : Auth P M₂ S₂}
    {s : Scenario P I (M₁ ⊕ M₂)} (hV : s.AuthValid G (A.seq R f B) (Auth.seq A₁ A₂)) :
    (s.seqFst R).AuthValid G A A₁ := by
  intro r b q m hb hq hadj hm τ hτ
  simp only [Scenario.seqFst] at hm
  split_ifs at hm with hrR
  · obtain ⟨m₀, hm₀, hm₀l⟩ := Option.bind_eq_some_iff.1 hm
    cases m₀ with
    | inr m₂ => simp at hm₀l
    | inl m₁ =>
      simp only [Sum.getLeft?_inl, Option.some.injEq] at hm₀l
      subst hm₀l
      rcases hV r b q _ hb hq hadj hm₀ (Sum.inl τ) ⟨τ, hτ, rfl⟩ with hs | hs
      · exact Or.inl hs
      · right
        obtain ⟨r', hr', p, hp, q', hadj', m', hm', hτ'⟩ := hs
        have hr'R : r' < R := lt_of_le_of_lt hr' hrR
        have hlen : (hist G (A.seq R f B) s r' p).length < R := by simpa using hr'R
        rw [seq_send_lt A R f B hlen] at hm'
        obtain ⟨m₁, hm₁, rfl⟩ := Option.map_eq_some_iff.1 hm'
        obtain ⟨τ', hτ'', hττ'⟩ := hτ'
        cases hττ'
        refine ⟨r', hr', p, hp, q', hadj', m₁, ?_, hτ''⟩
        rw [histL_hist_seq G A R f B s r' hr'R.le p] at hm₁
        exact hm₁

lemma Scenario.AuthValid.seqSnd {A₁ : Auth P M₁ S₁} {A₂ : Auth P M₂ S₂}
    {s : Scenario P I (M₁ ⊕ M₂)} (hV : s.AuthValid G (A.seq R f B) (Auth.seq A₁ A₂)) :
    (s.seqSnd R (seqInputs G A R f s)).AuthValid G B A₂ := by
  intro r b q m hb hq hadj hm τ hτ
  simp only [Scenario.seqSnd] at hm
  obtain ⟨m₀, hm₀, hm₀r⟩ := Option.bind_eq_some_iff.1 hm
  cases m₀ with
  | inl m₁ => simp at hm₀r
  | inr m₂ =>
    simp only [Sum.getRight?_inr, Option.some.injEq] at hm₀r
    subst hm₀r
    rcases hV (R + r) b q _ hb hq hadj hm₀ (Sum.inr τ) ⟨τ, hτ, rfl⟩ with hs | hs
    · exact Or.inl hs
    · right
      obtain ⟨r', hr', p, hp, q', hadj', m', hm', hτ'⟩ := hs
      by_cases hlt : r' < R
      · have hlen : (hist G (A.seq R f B) s r' p).length < R := by simpa using hlt
        rw [seq_send_lt A R f B hlen] at hm'
        obtain ⟨m₁, -, rfl⟩ := Option.map_eq_some_iff.1 hm'
        obtain ⟨τ', -, hττ'⟩ := hτ'
        cases hττ'
      · have hlen : R ≤ (hist G (A.seq R f B) s r' p).length := by simp; omega
        rw [seq_send_ge A R f B hlen] at hm'
        obtain ⟨m₂', hm₂', rfl⟩ := Option.map_eq_some_iff.1 hm'
        obtain ⟨τ', hτ'', hττ'⟩ := hτ'
        cases hττ'
        have hRr' : R ≤ r' := by omega
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hRr'
        refine ⟨k, by omega, p, hp, q', hadj', m₂', ?_, hτ''⟩
        rw [seqInput_hist G A R f B s k p, histR_hist_seq G A R f B s k p] at hm₂'
        exact hm₂'

/-! #### Signature structures on sum messages -/

lemma Auth.histTokens_left (A : Auth P (M₁ ⊕ M₂) S) {h : History P (M₁ ⊕ M₂)} {τ : S}
    (hτ : τ ∈ Auth.histTokens A.left (histL h)) : τ ∈ A.histTokens h := by
  obtain ⟨ib, hib, q, m, hm, hτm⟩ := hτ
  obtain ⟨ib₀, hib₀, rfl⟩ := List.mem_map.1 hib
  obtain ⟨m₀, hm₀, hm₀l⟩ := Option.bind_eq_some_iff.1 hm
  cases m₀ with
  | inl m₁ =>
    simp only [Sum.getLeft?_inl, Option.some.injEq] at hm₀l
    subst hm₀l
    exact ⟨ib₀, hib₀, q, Sum.inl m₁, hm₀, hτm⟩
  | inr m₂ => simp at hm₀l

lemma Auth.histTokens_right (A : Auth P (M₁ ⊕ M₂) S) {h : History P (M₁ ⊕ M₂)} {R : ℕ} {τ : S}
    (hτ : τ ∈ Auth.histTokens A.right (histR (h.drop R))) : τ ∈ A.histTokens h := by
  obtain ⟨ib, hib, q, m, hm, hτm⟩ := hτ
  obtain ⟨ib₀, hib₀, rfl⟩ := List.mem_map.1 hib
  obtain ⟨m₀, hm₀, hm₀r⟩ := Option.bind_eq_some_iff.1 hm
  cases m₀ with
  | inr m₂ =>
    simp only [Sum.getRight?_inr, Option.some.injEq] at hm₀r
    subst hm₀r
    exact ⟨ib₀, List.mem_of_mem_drop hib₀, q, Sum.inr m₂, hm₀, hτm⟩
  | inl m₁ => simp at hm₀r

variable {G A R f B}

/-- The sequential composition is unforging for any signature structure on `M₁ ⊕ M₂` whose left
and right parts make the two phases unforging. -/
lemma Protocol.Unforging.seq_of_left_right {Aut : Auth P (M₁ ⊕ M₂) S} (hA : A.Unforging Aut.left)
    (hB : B.Unforging Aut.right) : (A.seq R f B).Unforging Aut := by
  intro p x h q m hm τ hτ
  simp only [Protocol.seq] at hm
  split_ifs at hm with hlt
  · obtain ⟨m₁, hm₁, rfl⟩ := Option.map_eq_some_iff.1 hm
    exact (hA p x _ q m₁ hm₁ τ hτ).imp_right Aut.histTokens_left
  · obtain ⟨m₂, hm₂, rfl⟩ := Option.map_eq_some_iff.1 hm
    exact (hB p _ _ q m₂ hm₂ τ hτ).imp_right Aut.histTokens_right

variable (G A R f B) in
/-- The first phase of a run respecting unforgeability (for any signature structure on
`M₁ ⊕ M₂`) respects unforgeability for the left part of the structure. -/
lemma Scenario.AuthValid.seqFst_left {Aut : Auth P (M₁ ⊕ M₂) S} {s : Scenario P I (M₁ ⊕ M₂)}
    (hV : s.AuthValid G (A.seq R f B) Aut) : (s.seqFst R).AuthValid G A Aut.left := by
  intro r b q m hb hq hadj hm τ hτ
  simp only [Scenario.seqFst] at hm
  split_ifs at hm with hrR
  obtain ⟨m₀, hm₀, hm₀l⟩ := Option.bind_eq_some_iff.1 hm
  cases m₀ with
  | inr m₂ => simp at hm₀l
  | inl m₁ =>
    simp only [Sum.getLeft?_inl, Option.some.injEq] at hm₀l
    subst hm₀l
    rcases hV r b q _ hb hq hadj hm₀ τ hτ with hs | ⟨r', hr', p, hp, q', hadj', m', hm', hτ'⟩
    · exact Or.inl hs
    · right
      have hr'R : r' < R := lt_of_le_of_lt hr' hrR
      have hlen : (hist G (A.seq R f B) s r' p).length < R := by simpa using hr'R
      rw [seq_send_lt A R f B hlen] at hm'
      obtain ⟨m₁, hm₁, rfl⟩ := Option.map_eq_some_iff.1 hm'
      refine ⟨r', hr', p, hp, q', hadj', m₁, ?_, hτ'⟩
      rw [histL_hist_seq G A R f B s r' hr'R.le p] at hm₁
      exact hm₁

end Seq

end Cslib.Byzantine.LockStep
