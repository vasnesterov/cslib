/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Progress
public import Cslib.Computability.Distributed.SharedMemory.Linearization

/-!
# Indistinguishability and locality of steps

* `Impl.step_mem_local`: a step changes at most one base object.
* `Impl.Agree p C D`: `C` and `D` have the same memory and the same state of process `p`; then
  `p`'s solo executions from `C` and `D` coincide (`Impl.soloOp_eq_of_agree`).
* `Impl.Valid.allowed_of_mem`, `Impl.run_pend_eq_none_of_not_allowed`: processes that may not
  invoke anything stay idle.
* `Impl.HIwrtWith`: history independence with a fixed linearization function.

-/

@[expose] public section

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-- History independence w.r.t. `E`, for a fixed linearization function `h`. -/
def HIwrtWith (h : List (Label P A) → List (OpId P × A.Op))
    (E : List (Label P A) → Config A B P L → Prop) : Prop :=
  I.IsLinFun h ∧ ∀ α α' C C', I.run α = some C → I.run α' = some C' → E α C → E α' C' →
    linState (h α) = linState (h α') → C.mem = C'.mem

lemma hIwrt_iff (E : List (Label P A) → Config A B P L → Prop) :
    I.HIwrt E ↔ ∃ h, I.HIwrtWith h E := Iff.rfl

/-- Two memory representations differ in at most one base object (paper: distance `≤ 1`). -/
def MemDist1 (m m' : (i : ι) → (B i).State) : Prop :=
  ∀ j j', m j ≠ m' j → m j' ≠ m' j' → j = j'

omit [DecidableEq P] [DecidableEq ι] in
lemma MemDist1.symm {m m' : (i : ι) → (B i).State} (h : MemDist1 m m') : MemDist1 m' m :=
  fun j j' h1 h2 => h j j' (Ne.symm h1) (Ne.symm h2)

omit [DecidableEq P] [DecidableEq ι] in
lemma memDist1_refl (m : (i : ι) → (B i).State) : MemDist1 m m := fun _ _ h => absurd rfl h

variable {I}

/-- A step changes at most one base object. -/
lemma step_memDist1 {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C') :
    MemDist1 C.mem C'.mem := by
  cases ℓ with
  | inv p o => rw [(step_inv h).2.2.2.2]; exact memDist1_refl _
  | tau p =>
    obtain ⟨-, -, i, o, k, -, hm, -⟩ := step_tau h
    intro j j' h1 h2
    rw [hm] at h1 h2
    have e1 : j = i := by by_contra hne; exact h1 (by rw [Function.update_of_ne hne])
    have e2 : j' = i := by by_contra hne; exact h2 (by rw [Function.update_of_ne hne])
    rw [e1, e2]
  | ret p r => rw [(step_ret h).2.2.1]; exact memDist1_refl _

/-- `C` and `D` agree on the memory and on (the local state and pending operation of)
process `p`: `p` cannot distinguish them. -/
structure Agree (p : P) (C D : Config A B P L) : Prop where
  mem : C.mem = D.mem
  loc : C.loc p = D.loc p
  pend : C.pend p = D.pend p

omit [DecidableEq P] [DecidableEq ι] in
lemma Agree.symm {p : P} {C D : Config A B P L} (h : Agree p C D) : Agree p D C :=
  ⟨h.mem.symm, h.loc.symm, h.pend.symm⟩

variable (I) in
omit [DecidableEq P] [DecidableEq ι] in
lemma nextLabel_eq_of_agree {p : P} {C D : Config A B P L} (h : Agree p C D) :
    I.nextLabel C p = I.nextLabel D p := by
  unfold nextLabel; rw [h.loc]

/-- Steps of `p` from configurations `p` cannot distinguish lead to configurations `p` cannot
distinguish. -/
lemma step_agree {p : P} {C D C' : Config A B P L} (h : Agree p C D) {ℓ : Label P A}
    (hℓ : ℓ.proc = p) (hC : I.step C ℓ = some C') :
    ∃ D', I.step D ℓ = some D' ∧ Agree p C' D' := by
  classical
  cases ℓ with
  | inv q o =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨h0, h1, h2, h3, h4⟩ := step_inv hC
    have : I.step D (.inv q o) =
        some { D with pend := Function.update D.pend q (some o),
                      loc := Function.update D.loc q (I.invoke q (D.loc q) o) } := by
      simp [step, ← h.pend, h0, h1]
    refine ⟨_, this, ?_, ?_, ?_⟩
    · rw [h4, h.mem]
    · rw [h3]; simp [h.loc]
    · rw [h2]; simp
  | tau q =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨h0, h1, i, o, k, hact, hm, hl⟩ := step_tau hC
    have hact' : I.act q (D.loc q) = .access i o k := by rw [← h.loc, hact]
    have : I.step D (.tau q) = some { D with
        mem := Function.update D.mem i ((B i).δ (D.mem i) o).1,
        loc := Function.update D.loc q (k ((B i).δ (D.mem i) o).2) } := by
      simp [step, ← h.pend, h0, hact']
    refine ⟨_, this, ?_, ?_, ?_⟩
    · rw [hm, h.mem]
    · rw [hl]; simp [h.mem]
    · rw [h1]; exact h.pend
  | ret q r =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨h0, h1, h2, l, hact, hl⟩ := step_ret hC
    have hact' : I.act q (D.loc q) = .ret r l := by rw [← h.loc, hact]
    have : I.step D (.ret q r) = some { D with pend := Function.update D.pend q none,
                                               loc := Function.update D.loc q l } := by
      simp [step, ← h.pend, h0, hact']
    refine ⟨_, this, ?_, ?_, ?_⟩
    · rw [h2, h.mem]
    · rw [hl]; simp
    · rw [h1]; simp

lemma step_eq_none_iff_of_agree {p : P} {C D : Config A B P L} (h : Agree p C D) {ℓ : Label P A}
    (hℓ : ℓ.proc = p) : I.step C ℓ = none ↔ I.step D ℓ = none := by
  constructor
  · intro hC
    by_contra hD
    obtain ⟨D', hD'⟩ := Option.ne_none_iff_exists'.1 hD
    obtain ⟨C', hC', -⟩ := step_agree h.symm hℓ hD'
    rw [hC] at hC'; cases hC'
  · intro hD
    by_contra hC
    obtain ⟨C', hC'⟩ := Option.ne_none_iff_exists'.1 hC
    obtain ⟨D', hD', -⟩ := step_agree h hℓ hC'
    rw [hD] at hD'; cases hD'

lemma soloStep_agree {p : P} {C D : Config A B P L} (h : Agree p C D) :
    Agree p (I.soloStep p C) (I.soloStep p D) := by
  by_cases hp : C.pend p = none
  · have hp' : D.pend p = none := h.pend ▸ hp
    simp only [soloStep, hp, hp', ite_true]; exact h
  · have hp' : D.pend p ≠ none := h.pend ▸ hp
    obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 (I.step_nextLabel_isSome C p hp)
    obtain ⟨D', hD', hag⟩ := step_agree h (I.nextLabel_proc C p) hC'
    rw [nextLabel_eq_of_agree I h] at hD'
    have e1 : I.soloStep p C = C' := by simp [soloStep, hp, hC']
    have e2 : I.soloStep p D = D' := by
      simp [soloStep, hp', hD']
    rw [e1, e2]; exact hag

lemma iterate_soloStep_agree {p : P} {C D : Config A B P L} (h : Agree p C D) (k : ℕ) :
    Agree p ((I.soloStep p)^[k] C) ((I.soloStep p)^[k] D) := by
  induction k generalizing C D with
  | zero => exact h
  | succ k ih => simp only [Function.iterate_succ, Function.comp_apply]; exact ih (soloStep_agree h)

lemma soloLabels_eq_of_agree {p : P} {C D : Config A B P L} (h : Agree p C D) (k : ℕ) :
    I.soloLabels p C k = I.soloLabels p D k := by
  induction k generalizing C D with
  | zero => rfl
  | succ k ih =>
    rw [soloLabels_succ, soloLabels_succ, h.pend, nextLabel_eq_of_agree I h, ih (soloStep_agree h)]

lemma soloTime_eq_of_agree {p : P} {C D : Config A B P L} (h : Agree p C D) :
    I.soloTime p C = I.soloTime p D := by
  classical
  have hiff : ∀ k, ((I.soloStep p)^[k] C).pend p = none ↔ ((I.soloStep p)^[k] D).pend p = none :=
    fun k => by rw [(iterate_soloStep_agree h k).pend]
  have hex : (∃ k, ((I.soloStep p)^[k] C).pend p = none) ↔
      ∃ k, ((I.soloStep p)^[k] D).pend p = none := exists_congr hiff
  unfold soloTime
  by_cases h1 : ∃ k, ((I.soloStep p)^[k] C).pend p = none
  · have h2 := hex.1 h1
    rw [dite_eq_left_of_eq_true (eq_true h1), dite_eq_left_of_eq_true (eq_true h2)]
    apply le_antisymm
    · exact Nat.find_min' h1 ((hiff _).2 (Nat.find_spec h2))
    · exact Nat.find_min' h2 ((hiff _).1 (Nat.find_spec h1))
  · rw [dite_eq_right h1, dite_eq_right (fun h2 => h1 (hex.2 h2))]

/-- The solo execution of an operation of `p` only depends on what `p` can observe. -/
lemma soloOp_eq_of_agree {p : P} {C D : Config A B P L} (h : Agree p C D) (o : A.Op) :
    I.soloOp p o C = I.soloOp p o D := by
  unfold soloOp
  cases hC : I.step C (.inv p o) with
  | none =>
    rw [(step_eq_none_iff_of_agree h (rfl : (Label.inv p o).proc = p)).1 hC]
  | some C' =>
    obtain ⟨D', hD', hag⟩ := step_agree h rfl hC
    rw [hD']
    simp only
    rw [soloTime_eq_of_agree hag, soloLabels_eq_of_agree hag]

/-! ### Processes that may not invoke anything -/

lemma Valid.allowed_of_mem {α : List (Label P A)} (h : I.Valid α) {p : P} {o : A.Op}
    (hm : Label.inv p o ∈ α) : I.allowed p o := by
  obtain ⟨β, γ, rfl⟩ := List.append_of_mem hm
  obtain ⟨C, hC⟩ := h
  rw [run, runFrom_append] at hC
  cases h1 : I.runFrom I.initCfg β with
  | none => simp [h1] at hC
  | some C₁ =>
    simp only [h1, Option.bind_some, runFrom_cons] at hC
    cases h2 : I.step C₁ (.inv p o) with
    | none => simp [h2] at hC
    | some C₂ => exact (step_inv h2).2.1

lemma run_pend_eq_none_of_not_allowed {α : List (Label P A)} {C : Config A B P L}
    (h : I.run α = some C) {p : P} (hp : ∀ o, ¬ I.allowed p o) : C.pend p = none := by
  have hops : opsOf α p = [] := by
    simp only [opsOf, List.filterMap_eq_nil_iff]
    intro ℓ hℓ
    cases ℓ with
    | inv q o =>
      by_cases hq : q = p
      · subst hq; exact absurd ((Valid.allowed_of_mem ⟨C, h⟩ hℓ)) (hp o)
      · simp [hq]
    | ret q r => rfl
    | tau q => rfl
  rcases I.run_counts h p with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h1
  · rw [hops] at h2; simp at h2

/-- If along a run from `C` (with memory `M₀`) to `D` every intermediate memory is `M₀` or
`D.mem`, then `M₀` and `D.mem` differ in at most one base object (since each step changes at
most one). -/
lemma memDist1_of_run {γ : List (Label P A)} {C D : Config A B P L} {M₀ : (i : ι) → (B i).State}
    (hrun : I.runFrom C γ = some D) (hC : C.mem = M₀)
    (hmid : ∀ γ₁ γ₂ E, γ = γ₁ ++ γ₂ → I.runFrom C γ₁ = some E → E.mem = M₀ ∨ E.mem = D.mem) :
    MemDist1 M₀ D.mem := by
  induction γ generalizing C with
  | nil =>
    simp only [runFrom_nil, Option.some.injEq] at hrun
    subst hrun; rw [hC]; exact memDist1_refl _
  | cons ℓ γ ih =>
    simp only [runFrom_cons] at hrun
    cases hs : I.step C ℓ with
    | none => simp [hs] at hrun
    | some C₁ =>
      simp only [hs, Option.bind_some] at hrun
      rcases hmid [ℓ] γ C₁ rfl (by rw [runFrom_singleton, hs]) with h1 | h1
      · apply ih hrun h1
        intro γ₁ γ₂ E hγ hE
        apply hmid (ℓ :: γ₁) γ₂ E (by rw [hγ]; rfl)
        rw [runFrom_cons, hs, Option.bind_some, hE]
      · have := step_memDist1 hs
        rw [hC, h1] at this; exact this

/-- A sequential execution of `p` from the initial configuration: all other processes idle and
untouched, and every linearization ends in the state reached by `p`'s operations. -/
lemma soloOps_init_spec (hof : I.ObstructionFree) {h : List (Label P A) → List (OpId P × A.Op)}
    (hlin : I.IsLinFun h) (p : P) (os : List A.Op) (hos : ∀ o ∈ os, I.allowed p o) :
    ∃ C, I.run (I.soloOps p I.initCfg os) = some C ∧ C.Quiescent ∧
      linState (h (I.soloOps p I.initCfg os)) = A.runOps A.init os ∧
      (∀ q, q ≠ p → C.loc q = I.locInit q) ∧ opsOf (I.soloOps p I.initCfg os) p = os ∧
      (respsOf (I.soloOps p I.initCfg os) p).length = os.length ∧
      (∀ q, q ≠ p → opsOf (I.soloOps p I.initCfg os) q = []) ∧
      (∀ q, q ≠ p → respsOf (I.soloOps p I.initCfg os) q = []) := by
  obtain ⟨C, hrun, hc, hprocs, hops, hresps⟩ := I.soloOps_spec hof p os hos (α := []) rfl rfl
  have hne : ∀ q, q ≠ p → ∀ ℓ ∈ I.soloOps p I.initCfg os, ℓ.proc ≠ q :=
    fun q hq ℓ hℓ => by rw [hprocs ℓ hℓ]; exact Ne.symm hq
  have hother : ∀ q, q ≠ p → opsOf (I.soloOps p I.initCfg os) q = [] :=
    fun q hq => opsOf_eq_nil_of_proc_ne (hne q hq)
  refine ⟨C, hrun, ?_, ?_, ?_, hops, hresps, hother,
    fun q hq => respsOf_eq_nil_of_proc_ne (hne q hq)⟩
  · intro q
    by_cases hq : q = p
    · subst hq; exact hc
    · rw [(I.runFrom_other hrun (hne q hq)).2]; rfl
  · rw [(hlin _ ⟨_, hrun⟩).linState_of_changer (Valid.wellFormed I ⟨_, hrun⟩) p, hops]
    · intro q hq o ho; rw [hother q hq] at ho; simp at ho
    · rw [hops, hresps]
  · intro q hq; rw [(I.runFrom_other hrun (hne q hq)).1]; rfl

end Impl

end Cslib.SharedMemory
