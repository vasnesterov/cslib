/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Knowledge: indistinguishability systems, interpreted systems, common knowledge

The semantics of knowledge of Fagin–Halpern–Moses–Vardi (*Reasoning about Knowledge*), in two
layers.

**Indistinguishability systems** (`IndistSystem ι W`, S5 Kripke structures): a type `W` of
points and, for every agent `i : ι`, an equivalence relation `indist i` on points ("`i` has the
same view at both points"). A *fact* is a predicate `W → Prop`. On top of this:

* `K i φ` (knowledge), `IsLocal i φ` (facts determined by `i`'s view);
* for a *nonrigid set* of agents `N : W → Set ι` (e.g. the nonfaulty processes of the current run,
  or the nodes present in the current execution): nonfaulty knowledge
  `KN N i φ := i ∈ N ∧ K_i (i ∈ N → φ)` (Moses–Tuttle; David–Moses PODC 2026, Definition 1.1), the
  *hope* modality `Hope N i φ := i ∈ N → K_i (i ∈ N → φ)` (Kuznets et al.), everyone in `N` knows
  `E N φ := ⋀_{i ∈ N} K_i φ` and common knowledge `C N φ := ⋀_{m ≥ 1} (E N)^m φ`;
* **knowledge of preconditions** (`kop`, `kop_K`; Moses, TARK 2015);
* **common knowledge is truth along reachability** (`C_iff_forall_reach`): `C N φ` holds at `w`
  iff `φ` holds at every point reachable from `w` by a nonempty chain of `i`-indistinguishability
  steps with `i ∈ N` (the "similarity graph" of Halpern–Moses / Kuhn–Moses–Oshman).

**Interpreted systems** (`System ι R L`): runs `R`, local states `loc i r t : L i` and nonfaulty
sets `nf r`; a fact is a predicate on points `(r, t)` (`Fact R = R → ℕ → Prop`), a run fact a
predicate on runs (`RunFact.lift`). `System.toIndist` is the indistinguishability system on points
`R × ℕ` given by equality of local states; the modalities `System.K`, `KN`, `Hope`, `E`, `C` are
those of `toIndist` (curried), and `System.K_iff`, `isLocal_iff`, `E_iff`, `C_iff` unfold them to
the usual form.
-/

@[expose] public section

namespace Cslib.Knowledge

open Relation

/-! ### Indistinguishability systems -/

/-- An indistinguishability system: for every agent `i`, an equivalence relation `indist i` on the
points `W` (`indist i w w'`: `i` cannot distinguish `w` from `w'`). -/
structure IndistSystem (ι W : Type*) where
  /-- `indist i w w'`: agent `i` has the same view at `w` and `w'`. -/
  indist : ι → W → W → Prop
  /-- Each `indist i` is an equivalence relation. -/
  equiv : ∀ i, Equivalence (indist i)

namespace IndistSystem

variable {ι W : Type*} (M : IndistSystem ι W)

/-- `K i φ`: agent `i` knows `φ` at `w` iff `φ` holds at every point `i` cannot distinguish from
`w`. -/
def K (i : ι) (φ : W → Prop) : W → Prop := fun w => ∀ w', M.indist i w w' → φ w'

/-- A fact is *local to `i`* if it only depends on `i`'s view. -/
def IsLocal (i : ι) (φ : W → Prop) : Prop := ∀ w w', M.indist i w w' → (φ w ↔ φ w')

/-- **Nonfaulty knowledge** `K_i^N φ := i ∈ N ∧ K_i (i ∈ N → φ)` w.r.t. the nonrigid set `N`. -/
def KN (N : W → Set ι) (i : ι) (φ : W → Prop) : W → Prop :=
  fun w => i ∈ N w ∧ M.K i (fun w' => i ∈ N w' → φ w') w

/-- The **hope** modality `H_i φ := i ∈ N → K_i (i ∈ N → φ)` of Kuznets et al. -/
def Hope (N : W → Set ι) (i : ι) (φ : W → Prop) : W → Prop :=
  fun w => i ∈ N w → M.K i (fun w' => i ∈ N w' → φ w') w

/-- *Everyone in `N` knows*: `E_N φ := ⋀_{i ∈ N} K_i φ` (`N := fun _ => univ`: all agents). -/
def E (N : W → Set ι) (φ : W → Prop) : W → Prop := fun w => ∀ i ∈ N w, M.K i φ w

/-- *Common knowledge* among `N`: `C_N φ := (E_N)^m φ` for all `m ≥ 1`. -/
def C (N : W → Set ι) (φ : W → Prop) : W → Prop := fun w => ∀ m, (M.E N)^[m + 1] φ w

/-- One step of the similarity graph: some agent of `N` (at `w`) cannot distinguish `w` from `w'`.
-/
def Reach (N : W → Set ι) (w w' : W) : Prop := ∃ i ∈ N w, M.indist i w w'

variable {M}

/-- Every agent has the same view at a point as at itself. -/
theorem indist_refl (M : IndistSystem ι W) (i : ι) (w : W) : M.indist i w w := (M.equiv i).refl w

/-- Indistinguishability is symmetric. -/
theorem indist_symm {i : ι} {w w' : W} (h : M.indist i w w') : M.indist i w' w :=
  (M.equiv i).symm h

/-- Indistinguishability is transitive. -/
theorem indist_trans {i : ι} {w w' w'' : W} (h₁ : M.indist i w w') (h₂ : M.indist i w' w'') :
    M.indist i w w'' := (M.equiv i).trans h₁ h₂

/-! #### Knowledge -/

variable {i : ι} {N : W → Set ι} {φ ψ : W → Prop} {w : W}

/-- Knowledge axiom `K_i φ → φ`. -/
theorem K.holds (h : M.K i φ w) : φ w := h w (indist_refl M i w)

/-- Knowledge is monotone (only the points `i` considers possible matter). -/
theorem K.mono (h : M.K i φ w) (hφψ : ∀ w', M.indist i w w' → φ w' → ψ w') : M.K i ψ w :=
  fun w' h' => hφψ w' h' (h w' h')

/-- Knowledge formulas are local. -/
theorem isLocal_K (i : ι) (φ : W → Prop) : M.IsLocal i (M.K i φ) := fun _ _ h =>
  ⟨fun hK _ h'' => hK _ (indist_trans h h''),
    fun hK _ h'' => hK _ (indist_trans (indist_symm h) h'')⟩

/-- Knowledge is determined by the view. -/
theorem K.of_indist {w' : W} (h : M.K i φ w) (he : M.indist i w w') : M.K i φ w' :=
  (isLocal_K i φ w w' he).1 h

/-- Positive introspection `K_i φ → K_i K_i φ`. -/
theorem K.introspect (h : M.K i φ w) : M.K i (M.K i φ) w := fun _ h' => h.of_indist h'

/-- Local facts are known when they hold. -/
theorem IsLocal.K (hφ : M.IsLocal i φ) (h : φ w) : M.K i φ w :=
  fun w' h' => (hφ w w' h').1 h

/-- **Knowledge of preconditions** (Moses): if `ψ` is a necessary condition for an `i`-local
action `α`, then `K_i ψ` is a necessary condition for it. -/
theorem kop_K {α : W → Prop} (hα : M.IsLocal i α) (hpre : ∀ w, α w → ψ w) :
    ∀ w, α w → M.K i ψ w :=
  fun w ha w' h' => hpre w' ((hα w w' h').1 ha)

/-! #### Nonfaulty knowledge and hope -/

/-- `⊨ K_i^N φ → φ`. -/
theorem KN.holds (h : M.KN N i φ w) : φ w := h.2.holds h.1

/-- Nonfaulty knowledge is monotone (only points where `i ∈ N` matter). -/
theorem KN.mono (h : M.KN N i φ w) (hφψ : ∀ w', i ∈ N w' → φ w' → ψ w') : M.KN N i ψ w :=
  ⟨h.1, h.2.mono fun w' _ h' hi => hφψ w' hi (h' hi)⟩

/-- Nonfaulty knowledge of a conjunction. -/
theorem KN.and (h₁ : M.KN N i φ w) (h₂ : M.KN N i ψ w) :
    M.KN N i (fun w => φ w ∧ ψ w) w :=
  ⟨h₁.1, fun w' h' hi => ⟨h₁.2 w' h' hi, h₂.2 w' h' hi⟩⟩

/-- Nonfaulty knowledge of a universally quantified fact. -/
theorem KN.forall {α : Sort*} {φ : α → W → Prop} (hi : i ∈ N w) (h : ∀ a, M.KN N i (φ a) w) :
    M.KN N i (fun w => ∀ a, φ a w) w :=
  ⟨hi, fun w' h' hi' a => (h a).2 w' h' hi'⟩

/-- Agents outside `N` have no nonfaulty knowledge. -/
theorem not_kn_of_notMem (hi : i ∉ N w) : ¬ M.KN N i φ w := fun h => hi h.1

/-- For agents in `N`, nonfaulty knowledge coincides with hope. -/
theorem kn_iff_hope (hi : i ∈ N w) : M.KN N i φ w ↔ M.Hope N i φ w :=
  ⟨fun h _ => h.2, fun h => ⟨hi, h hi⟩⟩

/-- For agents outside `N`, hope holds for every fact, even `False`. -/
theorem hope_of_notMem (hi : i ∉ N w) : M.Hope N i φ w := fun h => absurd h hi

/-- **Knowledge of preconditions for nonfaulty agents** (Moses; Theorem 1.2 of David–Moses): if
`α` is `i`-local and `ψ` is a precondition for a nonfaulty `i` performing `α`, then a nonfaulty `i`
performing `α` has nonfaulty knowledge of `ψ`. -/
theorem kop {α : W → Prop} (hα : M.IsLocal i α) (hpre : ∀ w, i ∈ N w → α w → ψ w) :
    ∀ w, i ∈ N w → α w → M.KN N i ψ w :=
  fun w hi ha => ⟨hi, kop_K hα (fun _ ha' hi' => hpre _ hi' ha') w ha⟩

/-! #### Everyone knows and common knowledge -/

/-- Everyone in `N` knows `φ` iff `φ` holds one similarity step away. -/
theorem E_iff_forall_reach : M.E N φ w ↔ ∀ w', M.Reach N w w' → φ w' :=
  ⟨fun h _ ⟨i, hi, h'⟩ => h i hi _ h', fun h i hi w' h' => h w' ⟨i, hi, h'⟩⟩

/-- **Common knowledge is truth along reachability**: `C_N φ` holds at `w` iff `φ` holds at every
point reachable from `w` by a nonempty chain of indistinguishability steps of agents in `N`. -/
theorem C_iff_forall_reach : M.C N φ w ↔ ∀ w', TransGen (M.Reach N) w w' → φ w' := by
  constructor
  · intro h w' hw'
    induction hw' using TransGen.head_induction_on with
    | single h' => exact E_iff_forall_reach.1 (h 0) _ h'
    | head h' _ ih =>
      refine ih fun m => ?_
      have := h (m + 1)
      rw [Function.iterate_succ_apply', E_iff_forall_reach] at this
      exact this _ h'
  · intro h m
    induction m generalizing w with
    | zero => exact E_iff_forall_reach.2 fun w' h' => h w' (.single h')
    | succ m ih =>
      rw [Function.iterate_succ_apply', E_iff_forall_reach]
      exact fun w' h' => ih fun w'' h'' => h w'' (h''.head h')

end IndistSystem

/-! ### Interpreted systems -/

/-- A fact: a predicate on points `(r, t)`. -/
abbrev Fact (R : Type*) := R → ℕ → Prop

/-- A run fact, seen as a fact whose truth does not depend on time. -/
def RunFact.lift {R : Type*} (p : R → Prop) : Fact R := fun r _ => p r

/-- A lifted run fact holds at a point iff it holds of the run. -/
@[simp] lemma RunFact.lift_apply {R : Type*} (p : R → Prop) (r : R) (t : ℕ) :
    RunFact.lift p r t ↔ p r := Iff.rfl

/-- `⊨ φ`: the fact `φ` holds at every point of the system. -/
def Fact.Valid {R : Type*} (φ : Fact R) : Prop := ∀ r t, φ r t

/-- An interpreted system over processes `ι` and runs `R`: local states (of type `L i` for
process `i`) at every point, and the set of nonfaulty processes of every run. -/
structure System (ι R : Type*) (L : ι → Type*) where
  /-- The local state of process `i` at time `t` of run `r`. -/
  loc : (i : ι) → R → ℕ → L i
  /-- The nonfaulty (correct) processes of a run (`N(r)`). -/
  nf : R → Set ι

namespace System

variable {ι R : Type*} {L : ι → Type*} (S : System ι R L)

/-- The indistinguishability system of an interpreted system: points `(r, t)`, and `i` cannot
distinguish two points iff its local states agree. -/
def toIndist : IndistSystem ι (R × ℕ) where
  indist i w w' := S.loc i w.1 w.2 = S.loc i w'.1 w'.2
  equiv _ := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

variable {S} in
/-- Indistinguishability in `toIndist` is equality of local states. -/
@[simp] theorem toIndist_indist {i : ι} {w w' : R × ℕ} :
    S.toIndist.indist i w w' ↔ S.loc i w.1 w.2 = S.loc i w'.1 w'.2 := Iff.rfl

/-- The nonfaulty processes at a point, as a nonrigid set. -/
def nfP (w : R × ℕ) : Set ι := S.nf w.1

/-- `K_i φ` (curried form of `toIndist.K`). -/
def K (i : ι) (φ : Fact R) : Fact R := fun r t => S.toIndist.K i (Function.uncurry φ) (r, t)

/-- `φ` is local to `i`. -/
def IsLocal (i : ι) (φ : Fact R) : Prop := S.toIndist.IsLocal i (Function.uncurry φ)

/-- **Nonfaulty knowledge** `K_i^N φ := i ∈ N ∧ K_i (i ∈ N → φ)`. -/
def KN (i : ι) (φ : Fact R) : Fact R :=
  fun r t => S.toIndist.KN S.nfP i (Function.uncurry φ) (r, t)

/-- The **hope** modality `H_i φ := i ∈ N → K_i (i ∈ N → φ)`. -/
def Hope (i : ι) (φ : Fact R) : Fact R :=
  fun r t => S.toIndist.Hope S.nfP i (Function.uncurry φ) (r, t)

/-- Classical *everyone knows* among all processes: `E φ := ⋀_i K_i φ`. -/
def E (φ : Fact R) : Fact R :=
  fun r t => S.toIndist.E (fun _ => Set.univ) (Function.uncurry φ) (r, t)

/-- Classical *common knowledge* among all processes. -/
def C (φ : Fact R) : Fact R :=
  fun r t => S.toIndist.C (fun _ => Set.univ) (Function.uncurry φ) (r, t)

variable {S}

/-! #### The usual (curried) forms -/

/-- `System.K` unfolded: `φ` holds at all points where `i` has the same local state. -/
theorem K_iff {i : ι} {φ : Fact R} {r : R} {t : ℕ} :
    S.K i φ r t ↔ ∀ r' t', S.loc i r' t' = S.loc i r t → φ r' t' :=
  ⟨fun h r' t' h' => h (r', t') h'.symm, fun h w' h' => h w'.1 w'.2 h'.symm⟩

/-- `System.IsLocal` unfolded. -/
theorem isLocal_iff {i : ι} {φ : Fact R} :
    S.IsLocal i φ ↔ ∀ r t r' t', S.loc i r' t' = S.loc i r t → (φ r' t' ↔ φ r t) :=
  ⟨fun h r t r' t' h' => (h (r, t) (r', t') h'.symm).symm,
    fun h w w' h' => (h w.1 w.2 w'.1 w'.2 h'.symm).symm⟩

/-- `System.KN` unfolded: `K_i^N φ = i ∈ N ∧ K_i (i ∈ N → φ)`. -/
theorem kn_iff {i : ι} {φ : Fact R} {r : R} {t : ℕ} :
    S.KN i φ r t ↔ i ∈ S.nf r ∧ S.K i (fun r' t' => i ∈ S.nf r' → φ r' t') r t := Iff.rfl

/-- `System.Hope` unfolded: `H_i φ = i ∈ N → K_i (i ∈ N → φ)`. -/
theorem hope_iff {i : ι} {φ : Fact R} {r : R} {t : ℕ} :
    S.Hope i φ r t ↔ (i ∈ S.nf r → S.K i (fun r' t' => i ∈ S.nf r' → φ r' t') r t) := Iff.rfl

/-- `System.E` unfolded: every process knows `φ`. -/
theorem E_iff {φ : Fact R} {r : R} {t : ℕ} : S.E φ r t ↔ ∀ i, S.K i φ r t :=
  ⟨fun h i => h i trivial, fun h i _ => h i⟩

/-- Iterating `System.E` commutes with uncurrying. -/
theorem uncurry_iterate_E (φ : Fact R) (m : ℕ) :
    Function.uncurry ((S.E)^[m] φ) =
      (S.toIndist.E fun _ => Set.univ)^[m] (Function.uncurry φ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

/-- `System.C` unfolded: `E^m φ` for all `m ≥ 1`. -/
theorem C_iff {φ : Fact R} {r : R} {t : ℕ} : S.C φ r t ↔ ∀ m, (S.E)^[m + 1] φ r t := by
  simp only [C, IndistSystem.C]
  exact forall_congr' fun m => by rw [← uncurry_iterate_E]; rfl

/-- Common knowledge is truth along reachability (all processes). -/
theorem C_iff_forall_reach {φ : Fact R} {r : R} {t : ℕ} :
    S.C φ r t ↔ ∀ w', TransGen (S.toIndist.Reach fun _ => Set.univ) (r, t) w' → φ w'.1 w'.2 :=
  IndistSystem.C_iff_forall_reach

/-! #### Basic properties -/

/-- Knowledge axiom `K_i φ → φ`. -/
lemma K.holds {i : ι} {φ : Fact R} {r : R} {t : ℕ} (h : S.K i φ r t) : φ r t :=
  IndistSystem.K.holds (M := S.toIndist) (φ := Function.uncurry φ) (w := (r, t)) h

/-- Knowledge formulas are local. -/
lemma isLocal_K (i : ι) (φ : Fact R) : S.IsLocal i (S.K i φ) := fun w w' h =>
  IndistSystem.isLocal_K (M := S.toIndist) i (Function.uncurry φ) (w.1, w.2) (w'.1, w'.2) h

/-- `⊨ K_i^N φ → φ` (footnote 4 of David–Moses). -/
lemma KN.holds {i : ι} {φ : Fact R} {r : R} {t : ℕ} (h : S.KN i φ r t) : φ r t :=
  IndistSystem.KN.holds (M := S.toIndist) (φ := Function.uncurry φ) (w := (r, t)) h

/-- `⊨ i ∈ N ∧ K_i (i ∈ N → ψ) → ψ` (nonfaulty beliefs are never false). -/
lemma belief_true {i : ι} {φ : Fact R} {r : R} {t : ℕ} (hi : i ∈ S.nf r)
    (h : S.K i (fun r' t' => i ∈ S.nf r' → φ r' t') r t) : φ r t :=
  KN.holds ⟨hi, h⟩

/-- Nonfaulty knowledge is monotone. -/
lemma KN.mono {i : ι} {φ ψ : Fact R} {r : R} {t : ℕ} (h : S.KN i φ r t)
    (hφψ : ∀ r' t', i ∈ S.nf r' → φ r' t' → ψ r' t') : S.KN i ψ r t :=
  IndistSystem.KN.mono h fun w' => hφψ w'.1 w'.2

/-- Nonfaulty knowledge of a conjunction. -/
lemma KN.and {i : ι} {φ ψ : Fact R} {r : R} {t : ℕ} (h₁ : S.KN i φ r t) (h₂ : S.KN i ψ r t) :
    S.KN i (fun r t => φ r t ∧ ψ r t) r t :=
  IndistSystem.KN.and h₁ h₂

/-- Nonfaulty knowledge of a universally quantified fact. -/
lemma KN.forall {α : Sort*} {i : ι} {φ : α → Fact R} {r : R} {t : ℕ}
    (hi : i ∈ S.nf r) (h : ∀ a, S.KN i (φ a) r t) : S.KN i (fun r t => ∀ a, φ a r t) r t :=
  IndistSystem.KN.forall (φ := fun a => Function.uncurry (φ a)) hi h

/-- Faulty processes have no nonfaulty knowledge (footnote 4). -/
lemma not_kn_of_faulty {i : ι} {φ : Fact R} {r : R} {t : ℕ} (hi : i ∉ S.nf r) :
    ¬ S.KN i φ r t := IndistSystem.not_kn_of_notMem hi

/-- For nonfaulty processes, nonfaulty knowledge coincides with hope (footnote 4). -/
lemma kn_iff_hope {i : ι} {φ : Fact R} {r : R} {t : ℕ} (hi : i ∈ S.nf r) :
    S.KN i φ r t ↔ S.Hope i φ r t := IndistSystem.kn_iff_hope hi

/-- For faulty processes, hope holds for every fact, even `False` (footnote 4). -/
lemma hope_of_faulty {i : ι} {φ : Fact R} {r : R} {t : ℕ} (hi : i ∉ S.nf r) :
    S.Hope i φ r t := IndistSystem.hope_of_notMem hi

/-- **Knowledge of preconditions for nonfaulty processes** (Theorem 1.2 of David–Moses, an
instance of Moses' KoP principle): if the action `α` of process `i` is triggered by `i`'s local
state (`α` is `i`-local) and `ψ` is a precondition for a nonfaulty `i` performing `α`, then a
nonfaulty `i` performing `α` has nonfaulty knowledge of `ψ`. -/
theorem kop {i : ι} {α ψ : Fact R} (hα : S.IsLocal i α)
    (hpre : ∀ r t, i ∈ S.nf r → α r t → ψ r t) :
    ∀ r t, i ∈ S.nf r → α r t → S.KN i ψ r t :=
  fun r t => IndistSystem.kop (N := S.nfP) hα (fun w => hpre w.1 w.2) (r, t)

end System

end Cslib.Knowledge
