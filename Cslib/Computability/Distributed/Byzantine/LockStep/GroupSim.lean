/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.LockStep.Auth

/-!
# Group simulation: scaling a lock-step protocol down to fewer parties

A protocol for many parties `P` is turned into a protocol for few parties `Q`, given a surjective
*group map* `grp : P → Q` with representatives `rep : Q → P`: every party `q` simulates the group
`grp ⁻¹' {q}`. Messages between simulated parties of the same group are computed locally; messages
between groups are bundled (`GroupSim.Bundle P M`: for every simulated sender and receiver, a
message). This is the classical reduction "a protocol tolerating `t` faults among `n` parties gives
one tolerating `t / g` faults among `n / g` parties"; used e.g. for Lemma 3 of Constantinescu,
Dufay, Ghinea and Wattenhofer, *Byzantine Stable Matching* (PODC 2025).

## Main statements

* `GroupSim.hist_bigScenario` (simulation lemma): a run of the simulator against a Byzantine set
  `B` corresponds to a run of the simulated protocol against `grp ⁻¹' B` (with the induced
  adversary, `GroupSim.bigScenario`), in which every simulated party of an honest group has exactly
  the history its simulator reconstructs (`GroupSim.simHist`).
* `GroupSim.decides_proto`: an honest simulator decides what its representative decides.
* `GroupSim.Solvable.of_groupSim`: generic reduction (any party types, any specifications that
  transfer along the simulation).
* `GroupSim.authBundle`, `GroupSim.SolvableAuth.of_groupSim`: the authenticated version (a bundle
  carries the tokens of its messages; a token is signed by the group of its original signer).
-/

@[expose] public section

namespace Cslib.Byzantine.LockStep

namespace GroupSim

/-- What a simulator sends to another simulator: for every simulated sender and receiver, a
message (or nothing). -/
abbrev Bundle (P M : Type*) := P → P → Option M

variable {P Q I J O O' M : Type*}
variable (G : SimpleGraph P) (alg : Protocol P I M O) (grp : P → Q) (inp : Q → J → P → I)

open Classical in
/-- The histories of the simulated parties as reconstructed after `n` rounds by the simulator `q`
with input `x` and (own) history `h`. Messages from simulated parties of the own group are computed
locally, the others are read from the bundles received. -/
noncomputable def simHist (q : Q) (x : J) (h : History Q (Bundle P M)) : ℕ → P → History P M
  | 0, _ => []
  | n + 1, p => simHist q x h n p ++ [fun p₀ => if G.Adj p₀ p then
      (if grp p₀ = q then alg.send p₀ (inp q x p₀) (simHist q x h n p₀) p
       else (h[n]?).bind fun ib => (ib (grp p₀)).bind fun b => b p₀ p)
    else none]

open Classical in
/-- The simulating protocol: party `q` simulates the group `grp ⁻¹' {q}`, the simulated party of
`p` has input `inp q x p`; `q` decides (via `out q`) what its representative `rep q` decides. -/
noncomputable def proto (rep : Q → P) (out : Q → O → O') : Protocol Q J (Bundle P M) O' where
  send q x h q' := some fun p p' => if grp p = q ∧ grp p' = q' ∧ G.Adj p p' then
      alg.send p (inp q x p) (simHist G alg grp inp q x h h.length p) p' else none
  decide q x h := (alg.decide (rep q) (inp q x (rep q))
      (simHist G alg grp inp q x h h.length (rep q))).map (out q)

/-- The run of the simulated protocol induced by a run of the simulator: the Byzantine set is the
union of the Byzantine groups, and Byzantine simulated parties send what the bundles say. -/
def bigScenario (s : Scenario Q J (Bundle P M)) : Scenario P I M where
  byz := grp ⁻¹' s.byz
  input p := inp (grp p) (s.input (grp p)) p
  adv r p p' := (s.adv r (grp p) (grp p')).bind fun b => b p p'

/-- The induced run has no omissions. -/
lemma bigScenario_reliable (s : Scenario Q J (Bundle P M)) :
    (bigScenario grp inp s).Reliable := fun _ _ _ h => h

/-- Reconstructed histories only depend on the bundles received so far. -/
lemma simHist_append (q : Q) (x : J) (h : History Q (Bundle P M)) (ib : Inbox Q (Bundle P M)) :
    ∀ n ≤ h.length, simHist G alg grp inp q x (h ++ [ib]) n = simHist G alg grp inp q x h n := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    funext p
    simp only [simHist, ih (by omega), List.getElem?_append_left (show n < h.length by omega)]

open Classical in
/-- One more round of reconstruction from the last received bundles. -/
lemma simHist_append_succ (q : Q) (x : J) (h : History Q (Bundle P M)) (ib : Inbox Q (Bundle P M))
    {n : ℕ} (hn : h.length = n) (p : P) :
    simHist G alg grp inp q x (h ++ [ib]) (n + 1) p = simHist G alg grp inp q x h n p ++
      [fun p₀ => if G.Adj p₀ p then
        (if grp p₀ = q then alg.send p₀ (inp q x p₀) (simHist G alg grp inp q x h n p₀) p
         else (ib (grp p₀)).bind fun b => b p₀ p)
      else none] := by
  rw [simHist, simHist_append G alg grp inp q x h ib n hn.ge]
  subst hn
  simp

variable {G alg grp inp} {GQ : SimpleGraph Q} (rep : Q → P) (out : Q → O → O')

/-- **Simulation lemma**: in the induced run, every simulated party of an honest group has the
history reconstructed by its simulator. -/
theorem hist_bigScenario (hadj : ∀ p p', G.Adj p p' → grp p ≠ grp p' → GQ.Adj (grp p) (grp p'))
    (s : Scenario Q J (Bundle P M)) (hrel : s.Reliable) :
    ∀ r p, grp p ∉ s.byz → hist G alg (bigScenario grp inp s) r p =
      simHist G alg grp inp (grp p) (s.input (grp p))
        (hist GQ (proto G alg grp inp rep out) s r (grp p)) r p := by
  intro r
  induction r with
  | zero => intro p _; rfl
  | succ r ih =>
    intro p hp
    rw [hist_succ, hist_succ, simHist_append_succ G alg grp inp _ _ _ _ (length_hist _ _ _ _ _),
      ih p hp]
    congr 1
    refine congrArg (fun f => [f]) (funext fun p₀ => ?_)
    by_cases hA : G.Adj p₀ p
    · by_cases hg : grp p₀ = grp p
      · have hp₀ : grp p₀ ∉ s.byz := hg ▸ hp
        rw [deliver_honest _ _ _ (bigScenario_reliable grp inp s) hp₀ hA, ih p₀ hp₀]
        simp only [hA, hg, ↓reduceIte, bigScenario]
      · have hQ := hadj p₀ p hA hg
        simp only [hA, hg, ↓reduceIte]
        by_cases hb : grp p₀ ∈ s.byz
        · rw [deliver_byz _ _ (bigScenario grp inp s) hb hA, deliver_byz _ _ _ hb hQ]
          rfl
        · rw [deliver_honest _ _ _ (bigScenario_reliable grp inp s) hb hA,
            deliver_honest _ _ _ hrel hb hQ, ih p₀ hb]
          simp [proto, hA, bigScenario]
    · simp [deliver, hA]

/-- An honest simulator decides what its representative decides in the induced run. -/
theorem decides_proto (hrep : ∀ q, grp (rep q) = q)
    (hadj : ∀ p p', G.Adj p p' → grp p ≠ grp p' → GQ.Adj (grp p) (grp p'))
    (s : Scenario Q J (Bundle P M)) (hrel : s.Reliable) {q : Q} (hq : q ∉ s.byz) (o' : O') :
    Decides GQ (proto G alg grp inp rep out) s q o' ↔
      ∃ o, Decides G alg (bigScenario grp inp s) (rep q) o ∧ out q o = o' := by
  have key : ∀ r, status GQ (proto G alg grp inp rep out) s r q =
      (status G alg (bigScenario grp inp s) r (rep q)).map (out q) := by
    intro r
    have := hist_bigScenario (alg := alg) (inp := inp) rep out hadj s hrel r (rep q)
      (by rw [hrep]; exact hq)
    rw [hrep] at this
    simp only [status]
    rw [this]
    simp only [proto, length_hist, bigScenario, hrep]
  rw [decides_iff_firstSome, FirstSome.congr key, firstSome_map_iff]
  rfl

end GroupSim

namespace GroupSim

variable {P Q : Type} {I J O O' : Type*}

/-- **Generic group-simulation reduction.** If every simulated run against `grp ⁻¹' B` (`B ∈ ZQ`) is
admissible and the specification transfers along the simulation (honest groups, inputs `inp`,
decisions of the representatives translated by `out`), then solvability transfers from the large
system to the small one. -/
theorem Solvable.of_groupSim {GP : SimpleGraph P} {GQ : SimpleGraph Q} {ZP : AdvStructure P}
    {ZQ : AdvStructure Q} {specP : Spec P I O} {specQ : Spec Q J O'}
    (grp : P → Q) (rep : Q → P) (hrep : ∀ q, grp (rep q) = q) (inp : Q → J → P → I)
    (out : Q → O → O')
    (hadj : ∀ p p', GP.Adj p p' → grp p ≠ grp p' → GQ.Adj (grp p) (grp p'))
    (hZ : ∀ B ∈ ZQ, grp ⁻¹' B ∈ ZP)
    (hspec : ∀ (x : Q → J) (B : Set Q) (dec : P → O → Prop) (dec' : Q → O' → Prop),
      specP (fun p => inp (grp p) (x (grp p)) p) (grp ⁻¹' B)ᶜ dec →
      (∀ q ∉ B, ∀ o', dec' q o' ↔ ∃ o, dec (rep q) o ∧ out q o = o') →
      specQ x Bᶜ dec')
    (h : Solvable GP ZP specP) : Solvable GQ ZQ specQ := by
  obtain ⟨M, alg, halg⟩ := h
  exact ⟨Bundle P M, proto GP alg grp inp rep out, fun s hs hrel =>
    hspec s.input s.byz _ _
      (halg (bigScenario grp inp s) (hZ _ hs) (bigScenario_reliable grp inp s))
      fun q hq o' => decides_proto rep out hrep hadj s hrel hq o'⟩

end GroupSim

/-! ### Authenticated setting -/

namespace GroupSim

variable {P Q I J O O' M S : Type*}

/-- Signatures on bundles: a bundle contains the tokens of all its messages; the signer of a token
is (the simulator of) the group of its original signer. -/
def authBundle (A : Auth P M S) (grp : P → Q) : Auth Q (Bundle P M) S where
  signer τ := grp (A.signer τ)
  tokens b := {τ | ∃ p p' m, b p p' = some m ∧ τ ∈ A.tokens m}

variable {G : SimpleGraph P} {alg : Protocol P I M O} {grp : P → Q} {inp : Q → J → P → I}
  {A : Auth P M S}

/-- Tokens in reconstructed histories are signed by the own group or were received. -/
lemma histTokens_simHist (hU : alg.Unforging A) (q : Q) (x : J) (h : History Q (Bundle P M)) :
    ∀ n p, A.histTokens (simHist G alg grp inp q x h n p) ⊆
      {τ | grp (A.signer τ) = q} ∪ (authBundle A grp).histTokens h := by
  intro n
  induction n with
  | zero => intro p τ hτ; simp [simHist, Auth.histTokens] at hτ
  | succ n ih =>
    intro p τ hτ
    rw [simHist, Auth.histTokens_append] at hτ
    rcases hτ with hτ | ⟨ib, hib, p₀, m, hm, hτm⟩
    · exact ih p hτ
    · simp only [List.mem_singleton] at hib
      subst hib
      by_cases hA : G.Adj p₀ p
      · by_cases hg : grp p₀ = q
        · simp only [hA, hg, ↓reduceIte] at hm
          rcases hU _ _ _ _ _ hm τ hτm with hs | hs
          · exact Or.inl (show grp (A.signer τ) = q by rw [hs, hg])
          · exact ih p₀ hs
        · simp only [hA, hg, ↓reduceIte] at hm
          obtain ⟨ib, hib, hm⟩ := Option.bind_eq_some_iff.mp hm
          obtain ⟨b, hb, hm⟩ := Option.bind_eq_some_iff.mp hm
          exact Or.inr ⟨ib, List.mem_of_getElem? hib, grp p₀, b, hb, p₀, p, m, hm, hτm⟩
      · simp [hA] at hm

variable (rep : Q → P) (out : Q → O → O')

/-- The simulating protocol does not forge signatures (on bundles). -/
lemma unforging_proto (hU : alg.Unforging A) :
    (proto G alg grp inp rep out).Unforging (authBundle A grp) := by
  intro q x h q' b hb τ ⟨p, p', m, hm, hτm⟩
  simp only [proto, Option.some.injEq] at hb
  subst hb
  by_cases hc : grp p = q ∧ grp p' = q' ∧ G.Adj p p'
  · simp only [hc, and_self, ↓reduceIte] at hm
    rcases hU _ _ _ _ _ hm τ hτm with hs | hs
    · exact Or.inl (show grp (A.signer τ) = q by rw [hs, hc.1])
    · exact histTokens_simHist hU q x h _ p hs
  · simp [hc] at hm

variable {GQ : SimpleGraph Q}

/-- Tokens emitted by honest simulators are emitted by honest simulated parties. -/
lemma honestTokens_proto
    (hadj : ∀ p p', G.Adj p p' → grp p ≠ grp p' → GQ.Adj (grp p) (grp p'))
    (s : Scenario Q J (Bundle P M)) (hrel : s.Reliable) (r : ℕ) :
    honestTokens GQ (proto G alg grp inp rep out) (authBundle A grp) s r ⊆
      honestTokens G alg A (bigScenario grp inp s) r := by
  rintro τ ⟨r', hr', q₀, hq₀, q₁, -, b, hb, p, p', m, hm, hτm⟩
  simp only [proto, Option.some.injEq] at hb
  subst hb
  by_cases hc : grp p = q₀ ∧ grp p' = q₁ ∧ G.Adj p p'
  · simp only [hc, and_self, ↓reduceIte, length_hist] at hm
    obtain ⟨rfl, -, hpp'⟩ := hc
    refine ⟨r', hr', p, hq₀, p', hpp', m, ?_, hτm⟩
    rw [hist_bigScenario (inp := inp) rep out hadj s hrel r' p hq₀]
    exact hm
  · simp [hc] at hm

/-- The induced run respects unforgeability if the simulator's run does. -/
lemma authValid_bigScenario
    (hadj : ∀ p p', G.Adj p p' → grp p ≠ grp p' → GQ.Adj (grp p) (grp p'))
    (s : Scenario Q J (Bundle P M)) (hrel : s.Reliable)
    (hV : s.AuthValid GQ (proto G alg grp inp rep out) (authBundle A grp)) :
    (bigScenario grp inp s).AuthValid G alg A := by
  intro r b p m hb hp hbp hm τ hτ
  obtain ⟨bd, hbd, hm⟩ := Option.bind_eq_some_iff.mp hm
  have hg : grp b ≠ grp p := fun e => hp (show grp p ∈ s.byz from e ▸ hb)
  rcases hV r (grp b) (grp p) bd hb hp (hadj b p hbp hg) hbd τ ⟨b, p, m, hm, hτ⟩ with h | h
  · exact Or.inl h
  · exact Or.inr (honestTokens_proto rep out hadj s hrel r h)

end GroupSim

namespace GroupSim

variable {P Q : Type} {I J O O' : Type*}

/-- **Generic group-simulation reduction**, authenticated setting (same token type; a token's
signer is the group of its original signer). -/
theorem SolvableAuth.of_groupSim {GP : SimpleGraph P} {GQ : SimpleGraph Q} {ZP : AdvStructure P}
    {ZQ : AdvStructure Q} {specP : Spec P I O} {specQ : Spec Q J O'}
    (grp : P → Q) (rep : Q → P) (hrep : ∀ q, grp (rep q) = q) (inp : Q → J → P → I)
    (out : Q → O → O')
    (hadj : ∀ p p', GP.Adj p p' → grp p ≠ grp p' → GQ.Adj (grp p) (grp p'))
    (hZ : ∀ B ∈ ZQ, grp ⁻¹' B ∈ ZP)
    (hspec : ∀ (x : Q → J) (B : Set Q) (dec : P → O → Prop) (dec' : Q → O' → Prop),
      specP (fun p => inp (grp p) (x (grp p)) p) (grp ⁻¹' B)ᶜ dec →
      (∀ q ∉ B, ∀ o', dec' q o' ↔ ∃ o, dec (rep q) o ∧ out q o = o') →
      specQ x Bᶜ dec')
    (h : SolvableAuth GP ZP specP) : SolvableAuth GQ ZQ specQ := by
  obtain ⟨M, S, A, alg, hU, halg⟩ := h
  exact ⟨Bundle P M, S, authBundle A grp, proto GP alg grp inp rep out,
    unforging_proto rep out hU, fun s hs hrel hV =>
    hspec s.input s.byz _ _
      (halg (bigScenario grp inp s) (hZ _ hs) (bigScenario_reliable grp inp s)
        (authValid_bigScenario rep out hadj s hrel hV))
      fun q hq o' => decides_proto rep out hrep hadj s hrel hq o'⟩

end GroupSim

end Cslib.Byzantine.LockStep
