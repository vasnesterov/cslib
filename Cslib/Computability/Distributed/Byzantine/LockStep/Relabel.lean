/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.LockStep.Auth

/-!
# Renaming the parties

Solvability (unauthenticated and authenticated) is invariant under renaming the parties along an
equivalence `e : P ≃ P'` that is a graph isomorphism `G ≅ G'`
(`hG : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q`).

* `Protocol.relabel alg e : Protocol P I M O` runs, at `p : P`, the code of `e p : P'` of
  `alg : Protocol P' I M O` (inboxes are re-indexed by `e.symm`, destinations by `e`).
* `Scenario.relabel s e : Scenario P' I M` transports a scenario on `P` to `P'`.
* `hist_relabel`, `decides_relabel`: the run of the relabelled protocol is the relabelled run.
* `Solves.relabel`, `Solvable.relabel`, `SolvesAuth.relabel`, `SolvableAuth.relabel`.
-/

@[expose] public section

namespace Cslib.Byzantine.LockStep

variable {P P' I M O S : Type*}

/-- Re-index a history with inboxes indexed by `P` to one indexed by `P'` (`ib ↦ ib ∘ e.symm`). -/
abbrev relabelHist (e : P ≃ P') (h : History P M) : History P' M := h.map (· ∘ e.symm)

/-- Party `p` runs the code of `e p`. -/
def Protocol.relabel (alg : Protocol P' I M O) (e : P ≃ P') : Protocol P I M O where
  send p x h q := alg.send (e p) x (relabelHist e h) (e q)
  decide p x h := alg.decide (e p) x (relabelHist e h)

/-- Transport a scenario on `P` to `P'`. -/
def Scenario.relabel (s : Scenario P I M) (e : P ≃ P') : Scenario P' I M where
  byz := e '' s.byz
  input := s.input ∘ e.symm
  adv r p q := s.adv r (e.symm p) (e.symm q)
  drop r p q := s.drop r (e.symm p) (e.symm q)

namespace Scenario

variable (s : Scenario P I M) (e : P ≃ P')

@[simp] lemma relabel_input (p : P) : (s.relabel e).input (e p) = s.input p := by
  simp [Scenario.relabel]

@[simp] lemma mem_relabel_byz (p : P) : e p ∈ (s.relabel e).byz ↔ p ∈ s.byz := by
  simp [Scenario.relabel]

lemma relabel_honest : (s.relabel e).honest = e '' s.honest := by
  simp [Scenario.relabel, Scenario.honest, Set.image_compl_eq e.bijective]

lemma Reliable.relabel {s : Scenario P I M} (h : s.Reliable) : (s.relabel e).Reliable :=
  fun r p q => h r (e.symm p) (e.symm q)

end Scenario

section hist

variable {G : SimpleGraph P} {G' : SimpleGraph P'} (alg : Protocol P' I M O) (e : P ≃ P')
  (hG : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q) (s : Scenario P I M)
include hG

open Classical in
/-- The history of `e p` in the relabelled run is the relabelled history of `p`. -/
theorem hist_relabel (r : ℕ) (p : P) :
    hist G' alg (s.relabel e) r (e p) = relabelHist e (hist G (alg.relabel e) s r p) := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    rw [hist_succ, hist_succ, ih]
    simp only [relabelHist, List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    funext p'
    obtain ⟨q, rfl⟩ := e.surjective p'
    simp only [Function.comp_apply, Equiv.symm_apply_apply, deliver]
    by_cases hadj : G.Adj q p
    · simp only [(hG q p).mpr hadj, hadj, ite_true, Scenario.mem_relabel_byz]
      by_cases hq : q ∈ s.byz
      · simp [hq, Scenario.relabel]
      · simp only [hq, ite_false, ih, Scenario.relabel_input]
        simp only [Scenario.relabel, Equiv.symm_apply_apply, Protocol.relabel]
    · simp [hadj, (hG q p).not.mpr hadj]

theorem status_relabel (r : ℕ) (p : P) :
    status G' alg (s.relabel e) r (e p) = status G (alg.relabel e) s r p := by
  simp only [status, hist_relabel alg e hG, Scenario.relabel_input]
  rfl

/-- First decisions are preserved by relabelling. -/
theorem decides_relabel (p : P) (o : O) :
    Decides G (alg.relabel e) s p o ↔ Decides G' alg (s.relabel e) (e p) o := by
  simp only [decides_iff_firstSome, status_relabel alg e hG]

end hist

section solves

variable {G : SimpleGraph P} {G' : SimpleGraph P'} {alg : Protocol P' I M O} {e : P ≃ P'}
  {Z : AdvStructure P} {Z' : AdvStructure P'} {spec : Spec P I O} {spec' : Spec P' I O}

/-- Transport of a problem statement along a renaming. -/
lemma spec_relabel (hG : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q)
    (hspec : ∀ x H dec, spec' (x ∘ e.symm) (e '' H) (fun p' o => dec (e.symm p') o) →
      spec x H dec)
    (s : Scenario P I M) (h : spec' (s.relabel e).input (s.relabel e).honest
      (Decides G' alg (s.relabel e))) :
    spec s.input s.honest (Decides G (alg.relabel e) s) := by
  apply hspec
  have hd : Decides G' alg (s.relabel e) =
      fun p' o => Decides G (alg.relabel e) s (e.symm p') o := by
    funext p' o
    rw [decides_relabel alg e hG, Equiv.apply_symm_apply]
  rw [← hd, ← Scenario.relabel_honest]
  exact h

/-- Renaming the parties along a graph isomorphism `e : G ≅ G'` transports protocols. -/
theorem Solves.relabel (hG : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q)
    (h : Solves G' alg Z' spec') (hZ : ∀ B ∈ Z, e '' B ∈ Z')
    (hspec : ∀ x H dec, spec' (x ∘ e.symm) (e '' H) (fun p' o => dec (e.symm p') o) →
      spec x H dec) :
    Solves G (alg.relabel e) Z spec := fun s hs hrel =>
  spec_relabel hG hspec s (h (s.relabel e) (hZ _ hs) (hrel.relabel e))

/-- Solvability is invariant under renaming the parties along a graph isomorphism. -/
theorem Solvable.relabel (e : P ≃ P') (hG : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q)
    (h : Solvable G' Z' spec') (hZ : ∀ B ∈ Z, e '' B ∈ Z')
    (hspec : ∀ x H dec, spec' (x ∘ e.symm) (e '' H) (fun p' o => dec (e.symm p') o) →
      spec x H dec) :
    Solvable G Z spec := by
  obtain ⟨M, alg, h⟩ := h
  exact ⟨M, alg.relabel e, h.relabel hG hZ hspec⟩

end solves

/-! ### Authenticated setting -/

/-- The token structure seen from `P`: the signer `e.symm (A.signer τ)`. -/
def Auth.relabel (A : Auth P' M S) (e : P ≃ P') : Auth P M S where
  signer := e.symm ∘ A.signer
  tokens := A.tokens

lemma Auth.histTokens_relabel (A : Auth P' M S) (e : P ≃ P') (h : History P M) :
    (A.relabel e).histTokens h = A.histTokens (relabelHist e h) := by
  ext τ
  simp only [Auth.histTokens, Auth.relabel, relabelHist, List.mem_map, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ib, hib, p, m, hm, hτ⟩
    exact ⟨_, ⟨ib, hib, rfl⟩, e p, m, by simpa using hm, hτ⟩
  · rintro ⟨_, ⟨ib, hib, rfl⟩, p', m, hm, hτ⟩
    exact ⟨ib, hib, e.symm p', m, hm, hτ⟩

lemma Protocol.Unforging.relabel {A : Auth P' M S} {alg : Protocol P' I M O}
    (hU : alg.Unforging A) (e : P ≃ P') : (alg.relabel e).Unforging (A.relabel e) := by
  intro p x h q m hm τ hτ
  rcases hU _ _ _ _ _ hm τ hτ with hs | hs
  · left; simp [Auth.relabel, hs]
  · right; rwa [Auth.histTokens_relabel]

section auth

variable {G : SimpleGraph P} {G' : SimpleGraph P'} (alg : Protocol P' I M O) (e : P ≃ P')
  (hG : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q) (A : Auth P' M S) (s : Scenario P I M)
include hG

lemma honestTokens_relabel (r : ℕ) :
    honestTokens G (alg.relabel e) (A.relabel e) s r = honestTokens G' alg A (s.relabel e) r := by
  ext τ
  simp only [honestTokens, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨r', hr', p, hp, q, hpq, m, hm, hτ⟩
    refine ⟨r', hr', e p, by simpa using hp, e q, (hG p q).mpr hpq, m, ?_, hτ⟩
    rw [hist_relabel alg e hG, Scenario.relabel_input]
    exact hm
  · rintro ⟨r', hr', p', hp, q', hpq, m, hm, hτ⟩
    obtain ⟨p, rfl⟩ := e.surjective p'
    obtain ⟨q, rfl⟩ := e.surjective q'
    refine ⟨r', hr', p, by simpa using hp, q, (hG p q).mp hpq, m, ?_, hτ⟩
    rw [hist_relabel alg e hG, Scenario.relabel_input] at hm
    exact hm

lemma Scenario.authValid_relabel :
    s.AuthValid G (alg.relabel e) (A.relabel e) ↔ (s.relabel e).AuthValid G' alg A := by
  simp only [Scenario.AuthValid, honestTokens_relabel alg e hG]
  constructor
  · intro h r b' q' m hb hq hbq hm τ hτ
    obtain ⟨b, rfl⟩ := e.surjective b'
    obtain ⟨q, rfl⟩ := e.surjective q'
    rw [Scenario.mem_relabel_byz] at hb hq
    have := h r b q m hb hq ((hG b q).mp hbq)
      (by simpa [Scenario.relabel] using hm) τ hτ
    simpa [Auth.relabel, Scenario.relabel, Equiv.image_eq_preimage_symm] using this
  · intro h r b q m hb hq hbq hm τ hτ
    have := h r (e b) (e q) m (by simpa using hb) (by simpa using hq) ((hG b q).mpr hbq)
      (by simpa [Scenario.relabel] using hm) τ hτ
    simpa [Auth.relabel, Scenario.relabel, Equiv.image_eq_preimage_symm] using this

end auth

section solvesAuth

variable {G : SimpleGraph P} {G' : SimpleGraph P'} {alg : Protocol P' I M O} {e : P ≃ P'}
  {A : Auth P' M S}
  {Z : AdvStructure P} {Z' : AdvStructure P'} {spec : Spec P I O} {spec' : Spec P' I O}

/-- Renaming the parties transports authenticated protocols. -/
theorem SolvesAuth.relabel (hG : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q)
    (h : SolvesAuth G' alg A Z' spec') (hZ : ∀ B ∈ Z, e '' B ∈ Z')
    (hspec : ∀ x H dec, spec' (x ∘ e.symm) (e '' H) (fun p' o => dec (e.symm p') o) →
      spec x H dec) :
    SolvesAuth G (alg.relabel e) (A.relabel e) Z spec := fun s hs hrel hav =>
  spec_relabel hG hspec s (h (s.relabel e) (hZ _ hs) (hrel.relabel e)
    ((Scenario.authValid_relabel alg e hG A s).mp hav))

/-- Authenticated solvability is invariant under renaming the parties along a graph
isomorphism. -/
theorem SolvableAuth.relabel (e : P ≃ P') (hG : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q)
    (h : SolvableAuth G' Z' spec') (hZ : ∀ B ∈ Z, e '' B ∈ Z')
    (hspec : ∀ x H dec, spec' (x ∘ e.symm) (e '' H) (fun p' o => dec (e.symm p') o) →
      spec x H dec) :
    SolvableAuth G Z spec := by
  obtain ⟨M, S, A, alg, hU, h⟩ := h
  exact ⟨M, S, A.relabel e, alg.relabel e, hU.relabel e, h.relabel hG hZ hspec⟩

end solvesAuth

end Cslib.Byzantine.LockStep
