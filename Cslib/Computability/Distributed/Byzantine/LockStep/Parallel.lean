/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.LockStep.Agreement
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Finite.Lattice

/-!
# Parallel composition and output transformation of synchronous protocols

* `Protocol.parallel algs`: run a family of protocols `algs i` (possibly with different message
  types) in parallel, in lock-step. Messages are tuples `(i : ι) → Option (M i)`; the decision is
  the vector of the first decisions of all instances, taken as soon as every instance has decided.
  `hist_proj` identifies the projection of a run with a run of each instance in the projected
  scenario `s.proj i`, and `decides_parallel_iff` gives the decision correspondence.
* Authenticated version: `Auth.parallel` (tokens `Σ i, S i`), `Protocol.Unforging.parallel`,
  `Scenario.AuthValid.proj`.
* `IC_of_BB`, `IC_of_BB_auth`: running one Byzantine broadcast per party solves interactive
  consistency.
* `Protocol.mapOutput`: post-process decisions with a function `f : P → O → O'`.
-/

@[expose] public section

namespace Cslib.Byzantine.LockStep

/-! ### First decisions within a bounded horizon -/

section FirstUpTo

variable {O : Type*}

/-- The first `some` value among `f 0, …, f R`. -/
def firstUpTo (f : ℕ → Option O) : ℕ → Option O
  | 0 => f 0
  | R + 1 => (firstUpTo f R).or (f (R + 1))

lemma firstUpTo_eq_none {f : ℕ → Option O} {R : ℕ} :
    firstUpTo f R = none ↔ ∀ r ≤ R, f r = none := by
  induction R with
  | zero => simp [firstUpTo]
  | succ R ih =>
    simp only [firstUpTo, Option.or_eq_none_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ r hr
      rcases Nat.lt_or_eq_of_le hr with hr | rfl
      · exact h1 r (Nat.lt_succ_iff.1 hr)
      · exact h2
    · intro h
      exact ⟨fun r hr => h r (hr.trans (Nat.le_succ R)), h _ le_rfl⟩

lemma firstUpTo_congr {f g : ℕ → Option O} {R : ℕ} (hfg : ∀ r ≤ R, f r = g r) :
    firstUpTo f R = firstUpTo g R := by
  induction R with
  | zero => exact hfg 0 le_rfl
  | succ R ih =>
    simp only [firstUpTo]
    rw [ih fun r hr => hfg r (hr.trans (Nat.le_succ R)), hfg _ le_rfl]

lemma FirstSome.of_firstUpTo {f : ℕ → Option O} {R : ℕ} {o : O} (h : firstUpTo f R = some o) :
    FirstSome f o := by
  induction R with
  | zero => exact ⟨0, h, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ R ih =>
    simp only [firstUpTo] at h
    rcases hR : firstUpTo f R with _ | a
    · rw [hR, Option.none_or] at h
      refine ⟨R + 1, h, fun r' hr' => firstUpTo_eq_none.1 hR r' (Nat.lt_succ_iff.1 hr')⟩
    · rw [hR, Option.some_or] at h
      exact ih (hR.trans h)

lemma firstUpTo_of_firstSome {f : ℕ → Option O} {r : ℕ} {o : O} (hr : f r = some o)
    (hmin : ∀ r' < r, f r' = none) {R : ℕ} (hR : r ≤ R) : firstUpTo f R = some o := by
  induction R, hR using Nat.le_induction with
  | base =>
    cases r with
    | zero => exact hr
    | succ r =>
      simp only [firstUpTo]
      rw [firstUpTo_eq_none.2 fun r' hr' => hmin r' (Nat.lt_succ_of_le hr'), Option.none_or, hr]
  | succ R _ ih => simp only [firstUpTo, ih, Option.some_or]

lemma firstUpTo_eq_none_of_lt {f : ℕ → Option O} {r : ℕ} (hmin : ∀ r' < r, f r' = none) {R : ℕ}
    (hR : R < r) : firstUpTo f R = none :=
  firstUpTo_eq_none.2 fun r' hr' => hmin r' (lt_of_le_of_lt hr' hR)

end FirstUpTo

/-! ### Histories are prefixes of each other -/

lemma take_hist {P I M O : Type*} (G : SimpleGraph P) (alg : Protocol P I M O)
    (s : Scenario P I M) {j R : ℕ} (hj : j ≤ R) (p : P) :
    (hist G alg s R p).take j = hist G alg s j p := by
  induction R with
  | zero => rw [Nat.le_zero.1 hj]; rfl
  | succ R ih =>
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · rw [hist_succ, List.take_append_of_le_length (by simpa using Nat.lt_succ_iff.1 hj),
        ih (Nat.lt_succ_iff.1 hj)]
    · exact List.take_of_length_le (by simp)

/-! ### Collecting a family of options -/

section AllSome

variable {ι O : Type*}

open Classical in
/-- `some (fun i => oᵢ)` if every `f i = some oᵢ`, `none` otherwise. -/
noncomputable def allSome (f : ι → Option O) : Option (ι → O) :=
  if h : ∀ i, (f i).isSome then some fun i => (f i).get (h i) else none

lemma allSome_eq_some {f : ι → Option O} {d : ι → O} :
    allSome f = some d ↔ ∀ i, f i = some (d i) := by
  unfold allSome
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl i; simp
    · intro hd; funext i; simp [hd i]
  · simp only [false_iff]
    intro hd
    exact h fun i => by simp [hd i]

lemma allSome_eq_none {f : ι → Option O} : allSome f = none ↔ ∃ i, f i = none := by
  unfold allSome
  split_ifs with h
  · simp only [false_iff, not_exists]
    intro i hi; simpa [hi] using h i
  · simp only [true_iff]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact ⟨i, by simpa using hi⟩

end AllSome

/-! ### Parallel composition -/

section Parallel

variable {P I O ι : Type*} {M : ι → Type*}

/-- The `i`-th component of a product inbox. -/
def projInbox (i : ι) (ib : Inbox P ((j : ι) → Option (M j))) : Inbox P (M i) :=
  fun q => (ib q).bind (· i)

/-- The `i`-th component of a product history. -/
def projHist (i : ι) (h : History P ((j : ι) → Option (M j))) : History P (M i) :=
  h.map (projInbox i)

@[simp] lemma length_projHist (i : ι) (h : History P ((j : ι) → Option (M j))) :
    (projHist i h).length = h.length := List.length_map _

/-- The first decision of `alg` along the prefixes of the history `h`. -/
def Protocol.firstDecide {M' : Type*} (alg : Protocol P I M' O) (p : P) (x : I)
    (h : History P M') : Option O :=
  firstUpTo (fun j => alg.decide p x (h.take j)) h.length

/-- Parallel composition: run all `algs i` side by side; decide the vector of first decisions once
every instance has decided. Every party always sends a (tuple) message. -/
noncomputable def Protocol.parallel (algs : (i : ι) → Protocol P I (M i) O) :
    Protocol P I ((i : ι) → Option (M i)) (ι → O) where
  send p x h q := some fun i => (algs i).send p x (projHist i h) q
  decide p x h := allSome fun i => (algs i).firstDecide p x (projHist i h)

@[simp] lemma Protocol.parallel_send (algs : (i : ι) → Protocol P I (M i) O) (p : P) (x : I)
    (h : History P ((j : ι) → Option (M j))) (q : P) :
    (Protocol.parallel algs).send p x h q = some fun i => (algs i).send p x (projHist i h) q := rfl

/-- The scenario seen by instance `i`: same Byzantine set, inputs and omissions; the adversary's
messages are the `i`-th components. -/
def Scenario.proj (s : Scenario P I ((j : ι) → Option (M j))) (i : ι) : Scenario P I (M i) where
  byz := s.byz
  input := s.input
  adv r b q := (s.adv r b q).bind (· i)
  drop := s.drop

section ProjSimp
variable (s : Scenario P I ((j : ι) → Option (M j))) (i : ι)
@[simp] lemma Scenario.proj_byz : (s.proj i).byz = s.byz := rfl
@[simp] lemma Scenario.proj_input : (s.proj i).input = s.input := rfl
@[simp] lemma Scenario.proj_adv : (s.proj i).adv = fun r b q => (s.adv r b q).bind (· i) := rfl
@[simp] lemma Scenario.proj_drop : (s.proj i).drop = s.drop := rfl
@[simp] lemma Scenario.proj_honest : (s.proj i).honest = s.honest := rfl
lemma Scenario.Reliable.proj {s : Scenario P I ((j : ι) → Option (M j))} (h : s.Reliable) (i : ι) :
    (s.proj i).Reliable := h
end ProjSimp

variable (G : SimpleGraph P) (algs : (i : ι) → Protocol P I (M i) O)

/-- **Projection lemma**: the `i`-th component of a run of the parallel composition is the run of
`algs i` in the projected scenario. -/
lemma hist_proj (s : Scenario P I ((j : ι) → Option (M j))) (i : ι) (r : ℕ) (p : P) :
    projHist i (hist G (Protocol.parallel algs) s r p) = hist G (algs i) (s.proj i) r p := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    rw [hist_succ, hist_succ, projHist, List.map_append, ← projHist, ih]
    simp only [List.map_cons, List.map_nil]
    congr 2
    funext q
    simp only [projInbox, deliver, Scenario.proj_byz, Scenario.proj_adv, Scenario.proj_drop,
      Scenario.proj_input]
    by_cases hadj : G.Adj q p <;> by_cases hb : q ∈ s.byz <;> by_cases hd : s.drop r q p <;>
      simp [hadj, hb, hd, Protocol.parallel_send, ih]

lemma status_parallel (s : Scenario P I ((j : ι) → Option (M j))) (R : ℕ) (p : P) :
    status G (Protocol.parallel algs) s R p =
      allSome fun i => firstUpTo (fun j => status G (algs i) (s.proj i) j p) R := by
  unfold status
  change (allSome fun i => (algs i).firstDecide p (s.input p)
    (projHist i (hist G (Protocol.parallel algs) s R p))) = _
  congr 1
  funext i
  rw [hist_proj, Protocol.firstDecide, length_hist]
  exact firstUpTo_congr fun j hj => by rw [take_hist G _ _ hj]; rfl

open Classical in
/-- **Decision correspondence** for the parallel composition (any party, honest or not). -/
theorem decides_parallel_iff [Finite ι] (s : Scenario P I ((j : ι) → Option (M j))) (p : P)
    (d : ι → O) :
    Decides G (Protocol.parallel algs) s p d ↔ ∀ i, Decides G (algs i) (s.proj i) p (d i) := by
  simp only [decides_iff_firstSome, status_parallel]
  constructor
  · rintro ⟨R, hR, -⟩ i
    exact FirstSome.of_firstUpTo (allSome_eq_some.1 hR i)
  · intro h
    choose r hr hmin using h
    have hex : ∃ R, ∀ i, r i ≤ R := by
      obtain ⟨R, hR⟩ := (Set.finite_range r).bddAbove
      exact ⟨R, fun i => hR ⟨i, rfl⟩⟩
    refine ⟨Nat.find hex, allSome_eq_some.2 fun i =>
      firstUpTo_of_firstSome (hr i) (hmin i) (Nat.find_spec hex i), fun R' hR' => ?_⟩
    have := Nat.find_min hex hR'
    push Not at this
    obtain ⟨i, hi⟩ := this
    exact allSome_eq_none.2 ⟨i, firstUpTo_eq_none_of_lt (hmin i) hi⟩

/-! #### Authenticated parallel composition -/

/-- Product signature structure: a token of instance `i` is a pair `⟨i, τ⟩`. -/
def Auth.parallel {S : ι → Type*} (A : (i : ι) → Auth P (M i) (S i)) :
    Auth P ((i : ι) → Option (M i)) (Σ i, S i) where
  signer τ := (A τ.1).signer τ.2
  tokens m := {τ | ∃ mi, m τ.1 = some mi ∧ τ.2 ∈ (A τ.1).tokens mi}

variable {G algs}

lemma Auth.parallel_histTokens {S : ι → Type*} (A : (i : ι) → Auth P (M i) (S i)) (i : ι)
    (h : History P ((j : ι) → Option (M j))) {τ : S i} (hτ : τ ∈ (A i).histTokens (projHist i h)) :
    (⟨i, τ⟩ : Σ i, S i) ∈ (Auth.parallel A).histTokens h := by
  obtain ⟨ib, hib, p, m, hm, hτm⟩ := hτ
  obtain ⟨ib₀, hib₀, rfl⟩ := List.mem_map.1 hib
  obtain ⟨m₀, hm₀, hm₀i⟩ := Option.bind_eq_some_iff.1 hm
  exact ⟨ib₀, hib₀, p, m₀, hm₀, m, hm₀i, hτm⟩

lemma Protocol.Unforging.parallel {S : ι → Type*} {A : (i : ι) → Auth P (M i) (S i)}
    (hU : ∀ i, (algs i).Unforging (A i)) :
    (Protocol.parallel algs).Unforging (Auth.parallel A) := by
  rintro p x h q m hm ⟨i, τ⟩ ⟨mi, hmi, hτ⟩
  simp only [Protocol.parallel, Option.some.injEq] at hm
  subst hm
  rcases hU i p x _ q mi hmi τ hτ with hs | hs
  · exact Or.inl hs
  · exact Or.inr (Auth.parallel_histTokens A i h hs)

lemma Scenario.AuthValid.proj {S : ι → Type*} {A : (i : ι) → Auth P (M i) (S i)}
    {s : Scenario P I ((j : ι) → Option (M j))}
    (hV : s.AuthValid G (Protocol.parallel algs) (Auth.parallel A)) (i : ι) :
    (s.proj i).AuthValid G (algs i) (A i) := by
  intro r b q m hb hq hadj hm τ hτ
  simp only [Scenario.proj_adv] at hm
  obtain ⟨m₀, hm₀, hm₀i⟩ := Option.bind_eq_some_iff.1 hm
  rcases hV r b q m₀ hb hq hadj hm₀ ⟨i, τ⟩ ⟨m, hm₀i, hτ⟩ with hs | hs
  · exact Or.inl hs
  · right
    obtain ⟨r', hr', p, hp, q', hadj', m', hm', mi, hmi, hτ'⟩ := hs
    have e := Option.some.inj hm'
    subst e
    change (algs i).send p (s.input p) (projHist i (hist G (Protocol.parallel algs) s r' p)) q' =
      some mi at hmi
    rw [hist_proj] at hmi
    exact ⟨r', hr', p, hp, q', hadj', mi, hmi, hτ'⟩

end Parallel

/-! ### Interactive consistency from Byzantine broadcast -/

section IC

variable {P V : Type*}

/-- Spec-level reduction: if instance `i` satisfies `BB i` (on the same inputs and honest set) and
the decision relation is "decide the vector of the instances' decisions", then `IC` holds. -/
lemma IC_of_BB_spec (x : P → V) (H : Set P) (decI : P → P → V → Prop)
    (dec : P → (P → V) → Prop) (hBB : ∀ i, BB i x H (decI i))
    (hdec : ∀ p d, dec p d ↔ ∀ i, decI i p (d i)) : IC x H dec := by
  refine ⟨fun p hp => ?_, fun p hp d hd q hq => ?_, fun p hp q hq d e hd he => ?_⟩
  · choose v hv using fun i => (hBB i).1 p hp
    exact ⟨v, (hdec p v).2 hv⟩
  · exact (hBB q).2.2 p hp p hp _ _ ((hdec p d).1 hd q) ((hBB q).2.1 hq p hp)
  · funext i
    exact (hBB i).2.2 p hp q hq _ _ ((hdec p d).1 hd i) ((hdec q e).1 he i)

/-- Interactive consistency is solvable whenever Byzantine broadcast is solvable for every sender
(run one broadcast per party in parallel, each party broadcasting its own input). -/
theorem IC_of_BB {P : Type} [Finite P] {G : SimpleGraph P} {Z : AdvStructure P}
    (h : ∀ s : P, Solvable G Z (BB s : Spec P V V)) : Solvable G Z (IC : Spec P V (P → V)) := by
  choose M algs hs using h
  refine ⟨_, Protocol.parallel algs, fun s hZ hrel => ?_⟩
  exact IC_of_BB_spec s.input s.honest (fun i => Decides G (algs i) (s.proj i)) _
    (fun i => hs i (s.proj i) hZ (hrel.proj i)) (decides_parallel_iff G algs s)

/-- Authenticated version of `IC_of_BB`. -/
theorem IC_of_BB_auth {P : Type} [Finite P] {G : SimpleGraph P} {Z : AdvStructure P}
    (h : ∀ s : P, SolvableAuth G Z (BB s : Spec P V V)) :
    SolvableAuth G Z (IC : Spec P V (P → V)) := by
  choose M S A algs hU hs using h
  refine ⟨_, _, Auth.parallel A, Protocol.parallel algs, Protocol.Unforging.parallel hU,
    fun s hZ hrel hV => ?_⟩
  exact IC_of_BB_spec s.input s.honest (fun i => Decides G (algs i) (s.proj i)) _
    (fun i => hs i (s.proj i) hZ (hrel.proj i) (hV.proj i)) (decides_parallel_iff G algs s)

end IC

/-! ### Output transformation -/

section MapOutput

variable {P I M O O' S : Type*} (G : SimpleGraph P)

/-- Post-process the decisions of `alg` with `f p` (messages unchanged). -/
def Protocol.mapOutput (alg : Protocol P I M O) (f : P → O → O') : Protocol P I M O' where
  send := alg.send
  decide p x h := (alg.decide p x h).map (f p)

variable (alg : Protocol P I M O) (f : P → O → O')

lemma hist_mapOutput (s : Scenario P I M) : hist G (alg.mapOutput f) s = hist G alg s := by
  funext r
  induction r with
  | zero => rfl
  | succ r ih =>
    funext q
    rw [hist_succ, hist_succ, ih]
    rfl

lemma status_mapOutput (s : Scenario P I M) (r : ℕ) (p : P) :
    status G (alg.mapOutput f) s r p = (status G alg s r p).map (f p) := by
  simp only [status, hist_mapOutput]
  rfl

lemma decides_mapOutput (s : Scenario P I M) (p : P) (o' : O') :
    Decides G (alg.mapOutput f) s p o' ↔ ∃ o, Decides G alg s p o ∧ f p o = o' := by
  simp only [Decides, status_mapOutput]
  constructor
  · rintro ⟨r, hr, hmin⟩
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hr
    exact ⟨o, ⟨r, ho, fun r' hr' => Option.map_eq_none_iff.1 (hmin r' hr')⟩, rfl⟩
  · rintro ⟨o, ⟨r, ho, hmin⟩, rfl⟩
    exact ⟨r, by simp [ho], fun r' hr' => by simp [hmin r' hr']⟩

lemma Protocol.Unforging.mapOutput {A : Auth P M S} (hU : alg.Unforging A) :
    (alg.mapOutput f).Unforging A := hU

lemma Scenario.authValid_mapOutput (A : Auth P M S) (s : Scenario P I M) :
    s.AuthValid G (alg.mapOutput f) A ↔ s.AuthValid G alg A := by
  simp only [Scenario.AuthValid, honestTokens, hist_mapOutput]
  rfl

end MapOutput

end Cslib.Byzantine.LockStep
