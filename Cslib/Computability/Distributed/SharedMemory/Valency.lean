/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Consensus
public import Cslib.Computability.Distributed.SharedMemory.Covering
public import Mathlib.Data.Fintype.EquivFin

/-!
# Valency arguments for binary consensus

Bivalence arguments in the style of Fischer–Lynch–Paterson / Zhu (STOC'16) /
Ellen–Gelashvili–Shavit–Zhu (PODC'16) for obstruction-free binary consensus algorithms
`I : Impl BinCons B P L` (`BinCons = taskObj Bool Bool`).

## Main definitions

* `Steps Q β`: `β` consists of steps (no invocations) of processes in `Q` ("a `Q`-only execution").
* `Decides β v`: some process returns `v` in `β`.
* `CanDecide Q C v`: there is a `Q`-only execution from `C` in which `v` is decided (decisions made
  *before* `C` do not count). `CanDecide {p} C v` is "`p` decides `v` in its solo run from `C`".
* `Bivalent Q C`: `Q` can decide both values from `C`.
* `Reach C`: `C` is reached by a one-shot execution in which every process has been invoked (the
  "every process starts with an input" model).
* `ReachBy Q C C'`: `C'` is reachable from `C` by a `Q`-only execution.

## Main results

* `canDecide_of_agreeOn`: `CanDecide Q` only depends on the memory and the states of `Q`.
* `Reach.decides_eq` and variants: agreement along executions.
* `Reach.pend_of_bivalent`: if some set is bivalent, nobody has decided yet.
* `exists_canDecide_self`, `canDecide_self_unique`: a pending process decides exactly one value
  in its solo run (obstruction-freedom + determinism).
* `exists_initial` / `canDecide_initCfgOf` / `exists_initial_bivalent` (Lemma 6.4 of EGSZ'16): in
  the initial configuration where `p₀` has input `0` and `p₁` has input `1`, `p₀` decides `0` and
  `p₁` decides `1` solo.
* `exists_two_deciders` (Lemma 6.6 of EGSZ'16): if `U` is bivalent from `C`, a `U`-only execution
  reaches a configuration where two processes of `U` decide `0` and `1` in their solo runs.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace Cslib.SharedMemory

/-- The object specification of binary consensus: definitionally `taskObj Bool Bool`, but spelled
out as a reducible structure so that `BinCons.Resp` reduces to `Bool` for `simp` and instance
search (`taskObj` itself is not reducible). -/
abbrev BinCons : ObjSpec where
  State := Unit
  Op := Bool
  Resp := Bool
  init := ()
  δ _ _ := ((), default)

example : BinCons = taskObj Bool Bool := rfl

variable {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

/-- `β` consists of steps (internal steps and responses, no invocations) of processes of `Q`. -/
def Steps (Q : Set P) (β : List (Label P BinCons)) : Prop := ∀ ℓ ∈ β, ℓ.proc ∈ Q ∧ ℓ.IsStep

/-- Some process decides (returns) `v` in `β`. -/
def Decides (β : List (Label P BinCons)) (v : Bool) : Prop :=
  ∃ p, (Label.ret p v : Label P BinCons) ∈ β

omit [DecidableEq P] in
lemma Steps.nil (Q : Set P) : Steps Q ([] : List (Label P BinCons)) := by simp [Steps]

omit [DecidableEq P] in
lemma Steps.append {Q : Set P} {β γ : List (Label P BinCons)} (h1 : Steps Q β) (h2 : Steps Q γ) :
    Steps Q (β ++ γ) := by
  intro ℓ hℓ; rcases List.mem_append.1 hℓ with h | h
  · exact h1 ℓ h
  · exact h2 ℓ h

omit [DecidableEq P] in
lemma Steps.mono {Q Q' : Set P} {β : List (Label P BinCons)} (h : Steps Q β) (hQ : Q ⊆ Q') :
    Steps Q' β := fun ℓ hℓ => ⟨hQ (h ℓ hℓ).1, (h ℓ hℓ).2⟩

omit [DecidableEq P] in
lemma Steps.of_append_left {Q : Set P} {β γ : List (Label P BinCons)} (h : Steps Q (β ++ γ)) :
    Steps Q β := fun ℓ hℓ => h ℓ (List.mem_append_left _ hℓ)

omit [DecidableEq P] in
lemma Steps.of_append_right {Q : Set P} {β γ : List (Label P BinCons)} (h : Steps Q (β ++ γ)) :
    Steps Q γ := fun ℓ hℓ => h ℓ (List.mem_append_right _ hℓ)

omit [DecidableEq P] in
lemma Steps.of_prefix {Q : Set P} {β γ : List (Label P BinCons)} (h : Steps Q γ) (hp : β <+: γ) :
    Steps Q β := by
  obtain ⟨δ, rfl⟩ := hp; exact h.of_append_left

omit [DecidableEq P] in
lemma Steps.proc {Q : Set P} {β : List (Label P BinCons)} (h : Steps Q β) {ℓ} (hℓ : ℓ ∈ β) :
    ℓ.proc ∈ Q := (h ℓ hℓ).1

omit [DecidableEq P] in
lemma Steps.proc_ne {Q : Set P} {β : List (Label P BinCons)} (h : Steps Q β) {z : P}
    (hz : z ∉ Q) : ∀ ℓ ∈ β, ℓ.proc ≠ z := fun _ hℓ e => hz (e ▸ h.proc hℓ)

omit [DecidableEq P] in
lemma Steps.ret_proc {p : P} {β : List (Label P BinCons)} (hβ : Steps {p} β) {q : P} {v : Bool}
    (h : (Label.ret q v : Label P BinCons) ∈ β) : q = p := by
  simpa [Label.proc] using hβ.proc h

lemma Steps.opsOf_eq_nil {Q : Set P} {β : List (Label P BinCons)} (h : Steps Q β) (p : P) :
    opsOf β p = [] := by
  induction β with
  | nil => rfl
  | cons ℓ β ih =>
    have hℓ := (h ℓ (by simp)).2
    have ih := ih (fun ℓ' h' => h ℓ' (by simp [h']))
    cases ℓ with
    | inv q o => exact absurd hℓ (by simp [Label.IsStep])
    | ret q r => simp [opsOf_cons, ih]
    | tau q => simp [opsOf_cons, ih]

omit [DecidableEq P] in
lemma Decides.mono {β γ : List (Label P BinCons)} {v : Bool} (h : Decides β v) (hs : β ⊆ γ) :
    Decides γ v := by
  obtain ⟨p, hp⟩ := h; exact ⟨p, hs hp⟩

lemma mem_respsOf_iff {α : List (Label P BinCons)} {p : P} {v : Bool} :
    (v : BinCons.Resp) ∈ respsOf α p ↔ (Label.ret p v : Label P BinCons) ∈ α := by
  induction α with
  | nil => simp
  | cons ℓ α ih =>
    rw [respsOf_cons, List.mem_append, ih, List.mem_cons]
    cases ℓ with
    | inv q o => simp
    | tau q => simp
    | ret q r =>
      by_cases hq : q = p
      · subst hq
        simp only [Label.retOf_ret, ite_true, Option.toList_some, List.mem_singleton,
          Label.ret.injEq, true_and]
      · simp [hq, Ne.symm hq]

namespace Impl

variable (I : Impl BinCons B P L)

/-- `Q` can decide `v` from `C`: some `Q`-only execution from `C` decides `v`. -/
def CanDecide (Q : Set P) (C : Config BinCons B P L) (v : Bool) : Prop :=
  ∃ β C', Steps Q β ∧ I.runFrom C β = some C' ∧ Decides β v

/-- `Q` is bivalent from `C`. -/
def Bivalent (Q : Set P) (C : Config BinCons B P L) : Prop :=
  I.CanDecide Q C false ∧ I.CanDecide Q C true

/-- `C` is reached by a one-shot execution in which every process has been invoked. -/
def Reach (C : Config BinCons B P L) : Prop :=
  ∃ α, I.run α = some C ∧ OneShot α ∧ ∀ p, opsOf α p ≠ []

/-- `C'` is reachable from `C` by a `Q`-only execution. -/
def ReachBy (Q : Set P) (C C' : Config BinCons B P L) : Prop :=
  ∃ β, Steps Q β ∧ I.runFrom C β = some C'

variable {I}

lemma ReachBy.refl (Q : Set P) (C : Config BinCons B P L) : I.ReachBy Q C C :=
  ⟨[], Steps.nil Q, rfl⟩

lemma ReachBy.trans {Q : Set P} {C D E : Config BinCons B P L} (h1 : I.ReachBy Q C D)
    (h2 : I.ReachBy Q D E) : I.ReachBy Q C E := by
  obtain ⟨β, hβ, h⟩ := h1; obtain ⟨γ, hγ, h'⟩ := h2
  exact ⟨β ++ γ, hβ.append hγ, by rw [I.runFrom_append_of_eq h, h']⟩

lemma ReachBy.mono {Q Q' : Set P} {C D : Config BinCons B P L} (h : I.ReachBy Q C D)
    (hQ : Q ⊆ Q') : I.ReachBy Q' C D := by
  obtain ⟨β, hβ, h⟩ := h; exact ⟨β, hβ.mono hQ, h⟩

lemma ReachBy.of_steps {Q : Set P} {C D : Config BinCons B P L} {β : List (Label P BinCons)}
    (hβ : Steps Q β) (h : I.runFrom C β = some D) : I.ReachBy Q C D := ⟨β, hβ, h⟩

/-- Processes outside `Q` are unchanged by a `Q`-only execution. -/
lemma ReachBy.other {Q : Set P} {C D : Config BinCons B P L} (h : I.ReachBy Q C D) {z : P}
    (hz : z ∉ Q) : D.loc z = C.loc z ∧ D.pend z = C.pend z := by
  obtain ⟨β, hβ, h⟩ := h; exact I.runFrom_other h (hβ.proc_ne hz)

lemma Reach.extend {C C' : Config BinCons B P L} (hC : I.Reach C) {Q : Set P}
    {β : List (Label P BinCons)} (hβ : Steps Q β) (h : I.runFrom C β = some C') : I.Reach C' := by
  obtain ⟨α, hα, h1, h2⟩ := hC
  refine ⟨α ++ β, by rw [I.run_append_of_eq hα, h], fun p => ?_, fun p => ?_⟩
  · have := h1 p; simp only [opsOf_append, hβ.opsOf_eq_nil, List.append_nil]; exact this
  · simp only [opsOf_append, hβ.opsOf_eq_nil, List.append_nil]; exact h2 p

lemma Reach.reachBy {C C' : Config BinCons B P L} (hC : I.Reach C) {Q : Set P}
    (h : I.ReachBy Q C C') : I.Reach C' := by
  obtain ⟨β, hβ, h⟩ := h; exact hC.extend hβ h

/-! ### Responses in one-shot executions -/

lemma respsOf_length_le_one {α : List (Label P BinCons)} {C : Config BinCons B P L}
    (hα : I.run α = some C) (h1 : OneShot α) (p : P) : (respsOf α p).length ≤ 1 := by
  have := h1 p
  rcases I.run_counts hα p with ⟨-, h⟩ | ⟨-, h⟩ <;> omega

lemma ret_mem_unique {α : List (Label P BinCons)} {C : Config BinCons B P L}
    (hα : I.run α = some C) (h1 : OneShot α) {p : P} {v w : Bool}
    (hv : (Label.ret p v : Label P BinCons) ∈ α) (hw : (Label.ret p w : Label P BinCons) ∈ α) :
    v = w := by
  have hv' := mem_respsOf_iff.2 hv
  have hw' := mem_respsOf_iff.2 hw
  have hl := respsOf_length_le_one hα h1 p
  match h : respsOf α p, hl with
  | [], _ => rw [h] at hv'; simp at hv'
  | [x], _ =>
    rw [h] at hv' hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv' hw'
    rw [hv', hw']

lemma outputs_of_ret_mem {α : List (Label P BinCons)} {C : Config BinCons B P L}
    (hα : I.run α = some C) (h1 : OneShot α) {p : P} {v : Bool}
    (hv : (Label.ret p v : Label P BinCons) ∈ α) : outputs α p = some (v : BinCons.Resp) := by
  have hv' := mem_respsOf_iff.2 hv
  have hl := respsOf_length_le_one hα h1 p
  unfold outputs
  match h : respsOf α p, hl with
  | [], _ => rw [h] at hv'; simp at hv'
  | [x], _ =>
    rw [h] at hv'; simp only [List.mem_singleton] at hv'; subst hv'; rfl

variable (hS : I.Solves (weakConsensus P Bool))
include hS

/-- Agreement inside a single one-shot execution. -/
lemma decides_eq_of_run {α : List (Label P BinCons)} {C : Config BinCons B P L}
    (hα : I.run α = some C) (h1 : OneShot α) {v w : Bool} (hv : Decides α v)
    (hw : Decides α w) : v = w := by
  obtain ⟨p, hp⟩ := hv; obtain ⟨q, hq⟩ := hw
  exact (hS α ⟨C, hα⟩ h1).1 p q v w (outputs_of_ret_mem hα h1 hp) (outputs_of_ret_mem hα h1 hq)

/-- Agreement along an execution from a reachable configuration. -/
lemma Reach.decides_eq {C C' : Config BinCons B P L} (hC : I.Reach C) {Q : Set P}
    {β : List (Label P BinCons)} (hβ : Steps Q β) (h : I.runFrom C β = some C') {v w : Bool}
    (hv : Decides β v) (hw : Decides β w) : v = w := by
  obtain ⟨α, hα, h1, h2⟩ := hC
  refine decides_eq_of_run hS (α := α ++ β) (by rw [I.run_append_of_eq hα, h]) (fun p => ?_)
    (hv.mono (List.subset_append_right _ _)) (hw.mono (List.subset_append_right _ _))
  simp only [opsOf_append, hβ.opsOf_eq_nil, List.append_nil]; exact h1 p

/-- A decision in an execution from `C` and a later possible decision agree. -/
lemma Reach.decides_canDecide_eq {C C' : Config BinCons B P L} (hC : I.Reach C) {Q : Set P}
    {β : List (Label P BinCons)} (hβ : Steps Q β) (h : I.runFrom C β = some C') {v w : Bool}
    (hv : Decides β v) {Q' : Set P} (hw : I.CanDecide Q' C' w) : v = w := by
  obtain ⟨γ, D, hγ, hD, hw⟩ := hw
  exact hC.decides_eq hS (Q := Q ∪ Q') ((hβ.mono Set.subset_union_left).append
    (hγ.mono Set.subset_union_right)) (by rw [I.runFrom_append_of_eq h, hD])
    (hv.mono (List.subset_append_left _ _)) (hw.mono (List.subset_append_right _ _))

/-- If some set of processes is bivalent from a reachable configuration, nobody has decided yet:
every process is pending. -/
lemma Reach.pend_of_bivalent {C : Config BinCons B P L} (hC : I.Reach C) {Q : Set P}
    (hb : I.Bivalent Q C) (p : P) : C.pend p ≠ none := by
  intro hp
  obtain ⟨α, hα, h1, h2⟩ := hC
  have hc := I.run_counts hα p
  rw [hp] at hc
  simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false] at hc
  obtain ⟨u, hu⟩ : ∃ u, u ∈ respsOf α p := by
    match h : respsOf α p with
    | [] => rw [h] at hc; exact absurd (List.length_eq_zero_iff.1 hc) (h2 p)
    | x :: _ => exact ⟨x, by simp⟩
  have hb' : I.CanDecide Q C (!u) := by cases u; exacts [hb.2, hb.1]
  obtain ⟨β, C', hβ, hC', hd⟩ := hb'
  have := decides_eq_of_run hS (α := α ++ β) (by rw [I.run_append_of_eq hα, hC'])
    (fun q => by simp only [opsOf_append, hβ.opsOf_eq_nil, List.append_nil]; exact h1 q)
    (⟨p, List.mem_append_left _ (mem_respsOf_iff.1 hu)⟩ : Decides _ u)
    (hd.mono (List.subset_append_right _ _))
  cases u <;> simp at this

omit hS

/-! ### Basic properties of `CanDecide` -/

lemma CanDecide.mono {Q Q' : Set P} {C : Config BinCons B P L} {v : Bool}
    (h : I.CanDecide Q C v) (hQ : Q ⊆ Q') : I.CanDecide Q' C v := by
  obtain ⟨β, C', hβ, h1, h2⟩ := h; exact ⟨β, C', hβ.mono hQ, h1, h2⟩

lemma CanDecide.of_reachBy {Q : Set P} {C D : Config BinCons B P L} {v : Bool}
    (hr : I.ReachBy Q C D) (h : I.CanDecide Q D v) : I.CanDecide Q C v := by
  obtain ⟨β, hβ, hD⟩ := hr
  obtain ⟨γ, E, hγ, hE, hv⟩ := h
  exact ⟨β ++ γ, E, hβ.append hγ, by rw [I.runFrom_append_of_eq hD, hE],
    hv.mono (List.subset_append_right _ _)⟩

lemma canDecide_of_agreeOn {Q : Set P} {C D : Config BinCons B P L} (h : AgreeOn Q C D)
    {v : Bool} (hC : I.CanDecide Q C v) : I.CanDecide Q D v := by
  obtain ⟨β, C', hβ, h1, h2⟩ := hC
  obtain ⟨D', hD', -⟩ := I.runFrom_agreeOn h (fun ℓ hℓ => hβ.proc hℓ) h1
  exact ⟨β, D', hβ, hD', h2⟩

lemma canDecide_iff_of_agreeOn {Q : Set P} {C D : Config BinCons B P L} (h : AgreeOn Q C D)
    {v : Bool} : I.CanDecide Q C v ↔ I.CanDecide Q D v :=
  ⟨canDecide_of_agreeOn h, canDecide_of_agreeOn h.symm⟩

lemma bivalent_of_agreeOn {Q : Set P} {C D : Config BinCons B P L} (h : AgreeOn Q C D)
    (hC : I.Bivalent Q C) : I.Bivalent Q D :=
  ⟨canDecide_of_agreeOn h hC.1, canDecide_of_agreeOn h hC.2⟩

lemma Bivalent.mono {Q Q' : Set P} {C : Config BinCons B P L} (h : I.Bivalent Q C)
    (hQ : Q ⊆ Q') : I.Bivalent Q' C := ⟨h.1.mono hQ, h.2.mono hQ⟩

lemma canDecide_empty {C : Config BinCons B P L} {v : Bool} : ¬ I.CanDecide ∅ C v := by
  rintro ⟨β, C', hβ, -, p, hp⟩
  exact (hβ.proc hp)

lemma bivalent_of_canDecide {Q : Set P} {C : Config BinCons B P L} {a b : P} (ha : a ∈ Q)
    (hb : b ∈ Q) {v : Bool} (h1 : I.CanDecide {a} C v) (h2 : I.CanDecide {b} C (!v)) :
    I.Bivalent Q C := by
  cases v
  · exact ⟨h1.mono (by simpa using ha), h2.mono (by simpa using hb)⟩
  · exact ⟨h2.mono (by simpa using hb), h1.mono (by simpa using ha)⟩

/-! ### Solo decisions -/

omit [DecidableEq P] [DecidableEq ι] in
lemma nextLabel_isStep (C : Config BinCons B P L) (p : P) : (I.nextLabel C p).IsStep := by
  unfold nextLabel; split <;> trivial

lemma soloLabels_steps (p : P) (C : Config BinCons B P L) (k : ℕ) :
    Steps {p} (I.soloLabels p C k) := by
  induction k generalizing C with
  | zero => exact Steps.nil _
  | succ k ih =>
    rw [soloLabels_succ]
    split_ifs
    · exact Steps.nil _
    · intro ℓ hℓ
      rcases List.mem_cons.1 hℓ with rfl | hℓ
      · exact ⟨by simp [I.nextLabel_proc], nextLabel_isStep C p⟩
      · exact ih _ ℓ hℓ

lemma soloLabels_succ_eq_append (p : P) (C : Config BinCons B P L) (k : ℕ) :
    I.soloLabels p C (k + 1) = I.soloLabels p C k ++
      (if ((I.soloStep p)^[k] C).pend p = none then []
        else [I.nextLabel ((I.soloStep p)^[k] C) p]) := by
  induction k generalizing C with
  | zero => by_cases hp : C.pend p = none <;> simp [soloLabels, hp]
  | succ k ih =>
    rw [I.soloLabels_succ p C (k + 1), I.soloLabels_succ p C k, ih]
    by_cases hp : C.pend p = none
    · have hfix : ∀ j, (I.soloStep p)^[j] C = C := by
        intro j; induction j with
        | zero => rfl
        | succ j ihj => rw [Function.iterate_succ_apply', ihj]; simp [soloStep, hp]
      simp [hp, hfix]
    · simp only [hp, ite_false, Function.iterate_succ_apply, List.cons_append]
      split_ifs <;> simp_all

/-- By obstruction-freedom, a pending process decides some value in its solo run. -/
lemma Reach.exists_canDecide_self (hof : I.OneShotOF) {C : Config BinCons B P L}
    (hC : I.Reach C) {p : P} (hp : C.pend p ≠ none) : ∃ v, I.CanDecide {p} C v := by
  obtain ⟨α, hα, h1, -⟩ := hC
  obtain ⟨K, hK⟩ := hof α C p hα h1 hp
  have hrun := I.runFrom_soloLabels p C K
  have hc := I.runFrom_counts hrun p 1 0 (Or.inr ⟨hp, rfl⟩)
  rw [I.opsOf_soloLabels] at hc
  simp only [hK, List.length_nil, Nat.add_zero, Nat.zero_add, true_and, ne_eq, not_true_eq_false,
    false_and, or_false] at hc
  obtain ⟨v, hv⟩ : ∃ v, v ∈ respsOf (I.soloLabels p C K) p := by
    match h : respsOf (I.soloLabels p C K) p with
    | [] => rw [h] at hc; simp at hc
    | x :: _ => exact ⟨x, by simp⟩
  exact ⟨v, _, _, I.soloLabels_steps p C K, hrun, p, mem_respsOf_iff.1 hv⟩

/-- Two enabled steps of the same process from the same configuration are equal. -/
lemma step_eq_of_proc_eq {C C₁ C₂ : Config BinCons B P L} {ℓ ℓ' : Label P BinCons}
    (h : I.step C ℓ = some C₁) (h' : I.step C ℓ' = some C₂) (hp : ℓ.proc = ℓ'.proc)
    (hs : ℓ.IsStep) (hs' : ℓ'.IsStep) : ℓ = ℓ' := by
  classical
  cases ℓ with
  | inv q o => exact absurd hs (by simp [Label.IsStep])
  | tau q =>
    cases ℓ' with
    | inv q' o => exact absurd hs' (by simp [Label.IsStep])
    | tau q' => simp only [Label.proc] at hp; rw [hp]
    | ret q' r =>
      simp only [Label.proc] at hp; subst hp
      obtain ⟨-, -, i, o, k, hact, -⟩ := step_tau h
      obtain ⟨-, -, -, l, hact', -⟩ := step_ret h'
      rw [hact] at hact'; cases hact'
  | ret q r =>
    cases ℓ' with
    | inv q' o => exact absurd hs' (by simp [Label.IsStep])
    | tau q' =>
      simp only [Label.proc] at hp; subst hp
      obtain ⟨-, -, i, o, k, hact, -⟩ := step_tau h'
      obtain ⟨-, -, -, l, hact', -⟩ := step_ret h
      rw [hact] at hact'; cases hact'
    | ret q' r' =>
      simp only [Label.proc] at hp; subst hp
      obtain ⟨-, -, -, l, hact, -⟩ := step_ret h
      obtain ⟨-, -, -, l', hact', -⟩ := step_ret h'
      rw [hact] at hact'
      simp only [Action.ret.injEq] at hact'
      rw [hact'.1]

/-- Executions of a single process from the same configuration are comparable. -/
lemma steps_single_prefix {p : P} {C X Y : Config BinCons B P L} {β β' : List (Label P BinCons)}
    (h : I.runFrom C β = some X) (h' : I.runFrom C β' = some Y) (hβ : Steps {p} β)
    (hβ' : Steps {p} β') : β <+: β' ∨ β' <+: β := by
  induction β generalizing C β' with
  | nil => exact Or.inl (List.nil_prefix)
  | cons ℓ β ih =>
    cases β' with
    | nil => exact Or.inr (List.nil_prefix)
    | cons ℓ' β' =>
      simp only [runFrom_cons] at h h'
      cases hs : I.step C ℓ with
      | none => simp [hs] at h
      | some C₁ =>
        cases hs' : I.step C ℓ' with
        | none => simp [hs'] at h'
        | some C₂ =>
          simp only [hs, Option.bind_some] at h
          simp only [hs', Option.bind_some] at h'
          have hp : ℓ.proc = ℓ'.proc := by
            rw [show ℓ.proc = p from hβ.proc (by simp), show ℓ'.proc = p from hβ'.proc (by simp)]
          have heq := step_eq_of_proc_eq hs hs' hp (hβ ℓ (by simp)).2 (hβ' ℓ' (by simp)).2
          subst heq
          rw [hs] at hs'; cases hs'
          rcases ih h h' (fun x hx => hβ x (by simp [hx])) (fun x hx => hβ' x (by simp [hx]))
            with h1 | h1
          · exact Or.inl (List.cons_prefix_cons.2 ⟨rfl, h1⟩)
          · exact Or.inr (List.cons_prefix_cons.2 ⟨rfl, h1⟩)

/-- A process decides at most one value in its solo run. -/
lemma Reach.canDecide_self_unique {C : Config BinCons B P L} (hC : I.Reach C) {p : P}
    {v w : Bool} (hv : I.CanDecide {p} C v) (hw : I.CanDecide {p} C w) : v = w := by
  obtain ⟨β, X, hβ, hX, q, hq⟩ := hv
  obtain ⟨β', Y, hβ', hY, q', hq'⟩ := hw
  rw [hβ.ret_proc hq] at hq; rw [hβ'.ret_proc hq'] at hq'
  obtain ⟨α, hα, h1, -⟩ := hC
  have key : ∀ {γ Z}, I.runFrom C γ = some Z → Steps {p} γ → β <+: γ → β' <+: γ → v = w := by
    intro γ Z hZ hγ hp hp'
    refine ret_mem_unique (α := α ++ γ) (by rw [I.run_append_of_eq hα, hZ]) (fun r => ?_)
      (List.mem_append_right _ (hp.subset hq)) (List.mem_append_right _ (hp'.subset hq'))
    simp only [opsOf_append, hγ.opsOf_eq_nil, List.append_nil]; exact h1 r
  rcases steps_single_prefix hX hY hβ hβ' with h | h
  · exact key hY hβ' h (List.prefix_refl _)
  · exact key hX hβ (List.prefix_refl _) h

/-- The solo decision of a pending process. -/
lemma Reach.canDecide_self_iff (hof : I.OneShotOF) {C : Config BinCons B P L} (hC : I.Reach C)
    {p : P} (hp : C.pend p ≠ none) {v : Bool} : I.CanDecide {p} C v ↔ ¬ I.CanDecide {p} C (!v) := by
  constructor
  · intro h h'; have := hC.canDecide_self_unique h h'; cases v <;> simp at this
  · intro h
    obtain ⟨w, hw⟩ := hC.exists_canDecide_self hof hp
    cases v <;> cases w <;> simp_all

/-! ### Initial configurations (Lemma 6.4) -/

lemma runFrom_invs (f : P → Bool) :
    ∀ (ps : List P) (C : Config BinCons B P L), ps.Nodup → (∀ p ∈ ps, C.pend p = none) →
      (∀ p ∈ ps, I.allowed p (f p)) →
      ∃ C', I.runFrom C (ps.map fun p => (Label.inv p (f p) : Label P BinCons)) = some C' ∧
        (∀ q, C'.loc q = if q ∈ ps then I.invoke q (C.loc q) (f q) else C.loc q) ∧
        (∀ q, C'.pend q = if q ∈ ps then some (f q) else C.pend q) ∧ C'.mem = C.mem := by
  classical
  intro ps
  induction ps with
  | nil => intro C _ _ _; exact ⟨C, rfl, by simp, by simp, rfl⟩
  | cons p ps ih =>
    intro C hnd hpend hall
    have hs : I.step C (.inv p (f p)) = some { C with
        pend := Function.update C.pend p (some (f p)),
        loc := Function.update C.loc p (I.invoke p (C.loc p) (f p)) } := by
      simp [step, hpend p (by simp), hall p (by simp)]
    have hp : p ∉ ps := (List.nodup_cons.1 hnd).1
    obtain ⟨C', h1, h2, h3, h4⟩ := ih { C with
        pend := Function.update C.pend p (some (f p)),
        loc := Function.update C.loc p (I.invoke p (C.loc p) (f p)) } (List.nodup_cons.1 hnd).2
      (fun q hq => by
        have : q ≠ p := fun e => hp (e ▸ hq)
        simp [Function.update_of_ne this, hpend q (by simp [hq])])
      (fun q hq => hall q (by simp [hq]))
    refine ⟨C', by simp [hs, h1], fun q => ?_, fun q => ?_, h4⟩
    · rw [h2 q]
      by_cases hq : q ∈ ps
      · have : q ≠ p := fun e => hp (e ▸ hq)
        simp [hq, Function.update_of_ne this]
      · by_cases hqp : q = p
        · subst hqp; simp [hq]
        · simp [hq, hqp]
    · rw [h3 q]
      by_cases hq : q ∈ ps
      · simp [hq]
      · by_cases hqp : q = p
        · subst hqp; simp [hq]
        · simp [hq, hqp]

lemma respsOf_invs (f : P → Bool) (ps : List P) (q : P) :
    respsOf (ps.map fun p => (Label.inv p (f p) : Label P BinCons)) q = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [respsOf_cons, ih]

lemma opsOf_invs (f : P → Bool) (ps : List P) (q : P) :
    opsOf (ps.map fun p => (Label.inv p (f p) : Label P BinCons)) q =
      (ps.filter (· = q)).map f := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : p = q
    · subst h; simp [opsOf_cons, ih]
    · simp [opsOf_cons, ih, h]

section Init

variable [Fintype P]

/-- The labels invoking every process `p` with input `f p`. -/
noncomputable def initInvs (f : P → Bool) : List (Label P BinCons) :=
  (Finset.univ.toList).map fun p => (Label.inv p (f p) : Label P BinCons)

/-- The initial configuration in which every process `p` has been invoked with input `f p`
(the paper's "initial configuration with inputs `f`"). -/
lemma exists_initial (hall : ∀ p v, I.allowed p v) (f : P → Bool) :
    ∃ C, I.run (initInvs f) = some C ∧ I.Reach C ∧ (∀ p, C.loc p = I.invoke p (I.locInit p) (f p)) ∧
      (∀ p, C.pend p = some (f p)) ∧ C.mem = I.memInit := by
  obtain ⟨C, h1, h2, h3, h4⟩ := I.runFrom_invs f (Finset.univ.toList) I.initCfg
    (Finset.nodup_toList _) (fun _ _ => rfl) (fun p _ => hall p _)
  have hl : ∀ p, C.loc p = I.invoke p (I.locInit p) (f p) := fun p => by simp [h2 p, initCfg]
  have hp : ∀ p, C.pend p = some (f p) := fun p => by simp [h3 p]
  have hc : ∀ p, (opsOf (initInvs f) p).length = 1 := fun p => by
    rcases I.run_counts h1 p with ⟨h, -⟩ | ⟨-, h⟩
    · simp [hp p] at h
    · unfold initInvs; rw [h, respsOf_invs]; rfl
  refine ⟨C, h1, ⟨initInvs f, h1, fun p => (hc p).le, fun p h => ?_⟩, hl, hp, h4⟩
  have := hc p; rw [h] at this; simp at this

/-- **Weak validity in the initial configuration**: from the initial configuration with inputs
`f`, a process can only decide its own input in its solo run. -/
lemma canDecide_initial (hS : I.Solves (weakConsensus P Bool)) (hall : ∀ p v, I.allowed p v)
    (f : P → Bool) {C : Config BinCons B P L} (hC : I.run (initInvs f) = some C) {p : P} {w : Bool}
    (h : I.CanDecide {p} C w) : w = f p := by
  obtain ⟨C₀, h0, -, hl, hp, hm⟩ := I.exists_initial hall f
  rw [hC] at h0; cases h0
  obtain ⟨D, hD1, hD2, hD3, hD4⟩ := I.runFrom_invs f [p] I.initCfg (by simp) (fun _ _ => rfl)
    (fun q _ => hall q _)
  have hag : AgreeOn {p} C D := ⟨by rw [hm, hD4]; rfl, fun q hq => by
      rw [Set.mem_singleton_iff] at hq; subst hq; simp [hl, hD2, initCfg],
    fun q hq => by rw [Set.mem_singleton_iff] at hq; subst hq; simp [hp, hD3]⟩
  obtain ⟨β, D', hβ, hD', q, hq⟩ := canDecide_of_agreeOn hag h
  rw [hβ.ret_proc hq] at hq
  have hrun : I.run ([(Label.inv p (f p) : Label P BinCons)] ++ β) = some D' := by
    rw [run, runFrom_append,
      ← List.map_singleton (f := fun p => (Label.inv p (f p) : Label P BinCons)),
      hD1]; exact hD'
  have hops : ∀ q, opsOf ([(Label.inv p (f p) : Label P BinCons)] ++ β) q =
      if q = p then [f p] else [] := by
    intro q; by_cases hqp : q = p
    · subst hqp; simp [hβ.opsOf_eq_nil]
    · simp [hβ.opsOf_eq_nil, Ne.symm hqp, hqp]
  have h1 : OneShot ([(Label.inv p (f p) : Label P BinCons)] ++ β) := fun q => by
    rw [hops q]; split_ifs <;> simp
  refine (hS _ ⟨D', hrun⟩ h1).2 (f p) (fun q x hx => ?_) p w
    (outputs_of_ret_mem hrun h1 (List.mem_append_right _ hq))
  change (opsOf ([(Label.inv p (f p) : Label P BinCons)] ++ β) q).head? = some x at hx
  rw [hops q] at hx
  split_ifs at hx with hqp
  · simp at hx; exact hx.symm
  · simp at hx

omit [Fintype P] in
/-- **Lemma 6.4** of Ellen–Gelashvili–Shavit–Zhu: there is an initial configuration from which
`p₀` decides `0` and `p₁` decides `1` in their solo runs (so every set containing both is
bivalent). -/
theorem exists_initial_bivalent [Finite P] (hS : I.Solves (weakConsensus P Bool))
    (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v) {p₀ p₁ : P} (hne : p₀ ≠ p₁) :
    ∃ C, I.Reach C ∧ I.CanDecide {p₀} C false ∧ I.CanDecide {p₁} C true := by
  classical
  have := Fintype.ofFinite P
  let f : P → Bool := fun q => decide (q = p₁)
  obtain ⟨C, h1, hC, -, hp, -⟩ := I.exists_initial hall f
  obtain ⟨v₀, h₀⟩ := hC.exists_canDecide_self hof (p := p₀) (by simp [hp])
  obtain ⟨v₁, h₁⟩ := hC.exists_canDecide_self hof (p := p₁) (by simp [hp])
  have e₀ := canDecide_initial hS hall f h1 h₀
  have e₁ := canDecide_initial hS hall f h1 h₁
  simp only [f, hne, decide_false, decide_true] at e₀ e₁
  subst e₀; subst e₁
  exact ⟨C, hC, h₀, h₁⟩

lemma opsOf_initInvs (f : P → Bool) (q : P) : opsOf (initInvs f) q = [f q] := by
  simp only [initInvs, opsOf_invs]
  rw [List.filter_eq q, List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)]
  rfl

/-- **Weak validity from a unanimous initial configuration**: from any configuration reached from
the initial configuration in which every process has input `y`, only `y` can be decided. -/
lemma canDecide_const (hS : I.Solves (weakConsensus P Bool)) {y : Bool}
    {C₀ X : Config BinCons B P L} (h0 : I.run (initInvs fun _ => y) = some C₀) {Q' : Set P}
    (hX : I.ReachBy Q' C₀ X) {Q : Set P} {u : Bool} (hu : I.CanDecide Q X u) : u = y := by
  obtain ⟨β, hβ, hβr⟩ := hX
  obtain ⟨γ, Z, hγ, hZ, r, hr⟩ := hu
  have hrun : I.run (initInvs (fun _ => y) ++ (β ++ γ)) = some Z := by
    rw [I.run_append_of_eq h0, I.runFrom_append_of_eq hβr, hZ]
  have hops : ∀ q, opsOf (initInvs (fun _ => y) ++ (β ++ γ)) q = [y] := by
    intro q; simp [opsOf_initInvs, hβ.opsOf_eq_nil, hγ.opsOf_eq_nil]
  have h1 : OneShot (initInvs (fun _ => y) ++ (β ++ γ)) := fun q => by rw [hops]; simp
  refine (hS _ ⟨Z, hrun⟩ h1).2 y (fun q x hx => ?_) r u
    (outputs_of_ret_mem hrun h1 (by simp [hr]))
  change (opsOf (initInvs (fun _ => y) ++ (β ++ γ)) q).head? = some x at hx
  rw [hops] at hx; simp at hx; exact hx.symm

end Init

/-! ### Lemma 6.6: from bivalence to two solo deciders -/

lemma bivalent_of_canDecide_not {Q : Set P} {C : Config BinCons B P L} {v : Bool}
    (h1 : I.CanDecide Q C v) (h2 : I.CanDecide Q C (!v)) : I.Bivalent Q C := by
  cases v
  · exact ⟨h1, h2⟩
  · exact ⟨h2, h1⟩

lemma CanDecide.of_step {Q : Set P} {C C' : Config BinCons B P L} {δ : Label P BinCons}
    (hs : I.step C δ = some C') (hδ : δ.proc ∈ Q) (hδ' : δ.IsStep) {v : Bool}
    (h : I.CanDecide Q C' v) : I.CanDecide Q C v :=
  CanDecide.of_reachBy ⟨[δ], fun ℓ hℓ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
      subst hℓ; exact ⟨hδ, hδ'⟩,
    by rw [runFrom_singleton, hs]⟩ h

lemma Reach.canDecide_not_of_canDecide (hof : I.OneShotOF) {C : Config BinCons B P L}
    (hC : I.Reach C) {p : P} (hp : C.pend p ≠ none) {Q : Set P} (hpQ : p ∈ Q) {v : Bool}
    (h : ¬ I.CanDecide Q C v) : I.CanDecide {p} C (!v) := by
  obtain ⟨w, hw⟩ := hC.exists_canDecide_self hof hp
  have : w ≠ v := fun e => h (e ▸ hw.mono (by simpa using hpQ))
  cases w <;> cases v <;> simp_all

/-- **Lemma 6.6** of Ellen–Gelashvili–Shavit–Zhu (independent of the instruction set): if `U` is
bivalent from a reachable configuration `C`, then a `U`-only execution from `C` reaches a
configuration from which some process of `U` decides `0` and some process of `U` decides `1` in
their solo runs. -/
theorem Reach.exists_two_deciders (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF)
    {C : Config BinCons B P L} (hC : I.Reach C) (U : Finset P) (hU : I.Bivalent U C) :
    ∃ C', I.ReachBy U C C' ∧ ∃ q₀ ∈ U, ∃ q₁ ∈ U,
      I.CanDecide {q₀} C' false ∧ I.CanDecide {q₁} C' true := by
  classical
  have fin : ∀ {X : Config BinCons B P L} {a b : P} {v : Bool}, I.ReachBy U C X → a ∈ U → b ∈ U →
      I.CanDecide {a} X v → I.CanDecide {b} X (!v) → ∃ C', I.ReachBy U C C' ∧ ∃ q₀ ∈ U, ∃ q₁ ∈ U,
        I.CanDecide {q₀} C' false ∧ I.CanDecide {q₁} C' true := by
    intro X a b v hX ha hb h1 h2
    cases v
    · exact ⟨X, hX, a, ha, b, hb, h1, h2⟩
    · exact ⟨X, hX, b, hb, a, ha, h2, h1⟩
  have hex : ∃ k, ∃ X, ∃ U' : Finset P, I.ReachBy U C X ∧ I.Bivalent U X ∧ U' ⊆ U ∧
      I.Bivalent U' X ∧ U'.card = k :=
    ⟨U.card, C, U, ReachBy.refl _ _, hU, subset_rfl, hU, rfl⟩
  obtain ⟨X, U', hX, hXU, hU'U, hU'X, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ Y (U'' : Finset P), I.ReachBy U C Y → I.Bivalent U Y → U'' ⊆ U →
      I.Bivalent U'' Y → Nat.find hex ≤ U''.card :=
    fun Y U'' h1 h2 h3 h4 => Nat.find_min' hex ⟨Y, U'', h1, h2, h3, h4, rfl⟩
  have hXr : I.Reach X := hC.reachBy hX
  have hpend := hXr.pend_of_bivalent hS hXU
  obtain ⟨p, hp⟩ : U'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rintro rfl
    exact canDecide_empty (by simpa using hU'X.1)
  set U'' := U'.erase p with hU''
  have hU''sub : U'' ⊆ U := (Finset.erase_subset _ _).trans hU'U
  have hnb : ¬ I.Bivalent U'' X := fun h => by
    have h1 := hmin X U'' hX hXU hU''sub h
    have h2 := Finset.card_erase_of_mem hp
    have h3 := Finset.card_pos.2 ⟨p, hp⟩
    rw [← hU''] at h2; omega
  obtain ⟨q, hq⟩ : U''.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h0
    rw [hU'', Finset.erase_eq_empty_iff] at h0
    rcases h0 with h0 | h0
    · simp [h0] at hp
    · have h1 := hU'X.1; have h2 := hU'X.2
      rw [h0, Finset.coe_singleton] at h1 h2
      have := hXr.canDecide_self_unique h1 h2; simp at this
  have hpU : p ∈ U := hU'U hp
  have hqU : q ∈ U := hU''sub hq
  have hqU' : q ∈ U' := Finset.mem_of_mem_erase hq
  obtain ⟨v, hv⟩ : ∃ v, ¬ I.CanDecide U'' X (!v) := by
    by_cases h : I.CanDecide U'' X false
    · exact ⟨false, fun h' => hnb ⟨h, by simpa using h'⟩⟩
    · exact ⟨true, by simpa using h⟩
  have hqv : I.CanDecide {q} X v := by
    have := hXr.canDecide_not_of_canDecide hof (hpend q) (by simpa using hq) hv
    simpa using this
  obtain ⟨u, hu⟩ := hXr.exists_canDecide_self hof (hpend p)
  by_cases hu' : u = !v
  · subst hu'; exact fin hX hqU hpU hqv hu
  have hpv : I.CanDecide {p} X v := by
    have : u = v := by cases u <;> cases v <;> simp_all
    rw [← this]; exact hu
  clear hu hu' u
  -- an execution in which `!v` is decided
  have hU'nv : I.CanDecide U' X (!v) := by cases v; exacts [hU'X.2, hU'X.1]
  obtain ⟨β, Y, hβ, hY, r, hr⟩ := hU'nv
  have hexr : ∃ m, ∃ (h : m < β.length), ∃ q w, β[m] = (Label.ret q w : Label P BinCons) := by
    obtain ⟨m, hm, e⟩ := List.mem_iff_getElem.1 hr
    exact ⟨m, hm, r, !v, e⟩
  set m₀ := Nat.find hexr with hm₀def
  obtain ⟨hm₀, r₀, w₀, hr₀⟩ := Nat.find_spec hexr
  have hbefore : ∀ j < m₀, ∀ (h : j < β.length), ∀ q w,
      β[j] ≠ (Label.ret q w : Label P BinCons) := by
    intro j hj h q w e; exact Nat.find_min hexr hj ⟨h, q, w, e⟩
  have htau : ∀ j < m₀, ∀ (h : j < β.length), ∃ s, β[j] = (Label.tau s : Label P BinCons) := by
    intro j hj h
    have hs := (hβ β[j] (List.getElem_mem h)).2
    match e : β[j] with
    | .inv _ _ => rw [e] at hs; exact absurd hs (by simp [Label.IsStep])
    | .ret q w => exact absurd e (hbefore j hj h q w)
    | .tau s => exact ⟨s, rfl⟩
  have hw₀ : w₀ = !v := hXr.decides_eq hS hβ hY ⟨r₀, hr₀ ▸ List.getElem_mem hm₀⟩ ⟨r, hr⟩
  -- the configurations along `β`
  have hXm : ∀ m ≤ β.length, ∃ Z, I.runFrom X (β.take m) = some Z := by
    intro m _
    obtain ⟨Z, hZ, -⟩ := I.runFrom_eq_some_of_append (α := β.take m) (β := β.drop m)
      (by rw [List.take_append_drop]; exact hY)
    exact ⟨Z, hZ⟩
  have : Nonempty (Config BinCons B P L) := ⟨X⟩
  choose! Xm hXm using hXm
  have hstep : ∀ m (h : m < β.length), I.step (Xm m) β[m] = some (Xm (m + 1)) := by
    intro m h
    have e := hXm (m + 1) h
    rw [List.take_succ_eq_append_getElem h, I.runFrom_append_of_eq (hXm m h.le),
      runFrom_singleton] at e
    exact e
  have hXm0 : Xm 0 = X := by have := hXm 0 (Nat.zero_le _); simp at this; exact this.symm
  have hsteps : ∀ m ≤ β.length, Steps U' (β.take m) := fun m _ =>
    hβ.of_prefix (List.take_prefix _ _)
  have hreach : ∀ m ≤ β.length, I.Reach (Xm m) := fun m hm => hXr.extend (hsteps m hm) (hXm m hm)
  have hrb : ∀ m ≤ β.length, I.ReachBy U C (Xm m) := fun m hm =>
    hX.trans (ReachBy.of_steps ((hsteps m hm).mono (by simpa using hU'U)) (hXm m hm))
  have hpendm : ∀ m ≤ m₀, ∀ s, (Xm m).pend s ≠ none := by
    intro m hm s
    have hmβ : m ≤ β.length := by omega
    rw [I.runFrom_pend_of_tau (hXm m hmβ) (fun ℓ hℓ => by
      obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 hℓ
      rw [List.length_take] at hj
      rw [List.getElem_take] at e
      rw [← e]; exact htau j (by omega) _)]
    exact hpend s
  let G : ℕ → Prop := fun m => ¬ I.CanDecide {p} (Xm m) (!v) ∧ ¬ I.CanDecide U'' (Xm m) (!v)
  have hG0 : G 0 := by
    simp only [G]; rw [hXm0]
    exact ⟨fun h => by have := hXr.canDecide_self_unique hpv h; cases v <;> simp at this, hv⟩
  have hGend : ¬ G (m₀ + 1) := by
    intro ⟨h1, h2⟩
    have hR := hreach (m₀ + 1) hm₀
    -- a process other than `r₀` is still pending
    obtain ⟨s, hs, hsr⟩ : ∃ s, (s = p ∨ s ∈ U'') ∧ s ≠ r₀ := by
      by_cases e : r₀ = p
      · exact ⟨q, Or.inr hq, fun h => (Finset.ne_of_mem_erase hq) (h.trans e)⟩
      · exact ⟨p, Or.inl rfl, Ne.symm e⟩
    have hsp : (Xm (m₀ + 1)).pend s ≠ none := by
      have := hstep m₀ hm₀
      rw [hr₀] at this
      rw [(step_other this (by simpa [Label.proc] using Ne.symm hsr)).2]
      exact hpendm m₀ le_rfl s
    obtain ⟨w, hw⟩ := hR.exists_canDecide_self hof hsp
    have hwv : w₀ = w := hXr.decides_canDecide_eq hS (hsteps _ hm₀) (hXm _ hm₀)
      ⟨r₀, by rw [List.take_succ_eq_append_getElem hm₀, hr₀]; simp⟩ hw
    rw [← hwv, hw₀] at hw
    rcases hs with rfl | hs
    · exact h1 hw
    · exact h2 (hw.mono (by simpa using hs))
  set m := Nat.findGreatest G (m₀ + 1) with hmdef
  have hGm : G m := Nat.findGreatest_spec (P := G) (m := 0) (Nat.zero_le _) hG0
  have hmle : m ≤ m₀ := by
    have h1 := Nat.findGreatest_le (P := G) (m₀ + 1)
    have h2 : m ≠ m₀ + 1 := fun e => hGend (e ▸ hGm)
    omega
  have hGm1 : ¬ G (m + 1) :=
    Nat.findGreatest_is_greatest (P := G) (n := m₀ + 1) (k := m + 1) (by omega) (by omega)
  have hmβ : m < β.length := by omega
  have hs := hstep m hmβ
  have hδU' : β[m].proc ∈ (U' : Set P) := hβ.proc (List.getElem_mem hmβ)
  have hδS : β[m].IsStep := (hβ _ (List.getElem_mem hmβ)).2
  -- the next step is not a decision, hence `m < m₀`
  have hmlt : m < m₀ := by
    rcases Nat.lt_or_ge m m₀ with h | h
    · exact h
    · have e : m = m₀ := by omega
      exfalso
      have hβm : β[m] = (Label.ret r₀ (!v) : Label P BinCons) := by
        rw [← hw₀, ← hr₀]; simp [e, hm₀def]
      have hd : I.CanDecide {r₀} (Xm m) (!v) := ⟨[β[m]], Xm (m + 1),
        fun ℓ hℓ => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ; subst hℓ; refine ⟨?_, hδS⟩
          rw [hβm]; simp [Label.proc],
        by rw [runFrom_singleton, hs], r₀, by rw [hβm]; simp⟩
      have hr₀U' : r₀ ∈ U' := by
        have := hβ.proc (List.getElem_mem hm₀); rw [hr₀] at this; simpa [Label.proc] using this
      by_cases hr₀p : r₀ = p
      · subst hr₀p; exact hGm.1 hd
      · exact hGm.2 (hd.mono (by simpa [hU''] using And.intro hr₀U' hr₀p))
  have hR1 := hreach (m + 1) (by omega)
  have hpend1 := hpendm (m + 1) (by omega)
  have hrb1 := hrb (m + 1) (by omega)
  by_cases hsp : β[m].proc = p
  · -- the step is by `p`
    have hn1 : ¬ I.CanDecide {p} (Xm (m + 1)) (!v) := fun h =>
      hGm.1 (CanDecide.of_step hs (by simp [hsp]) hδS h)
    have hn2 : I.CanDecide U'' (Xm (m + 1)) (!v) := by
      by_contra h; exact hGm1 ⟨hn1, h⟩
    have hpv1 : I.CanDecide {p} (Xm (m + 1)) v := by
      have := hR1.canDecide_not_of_canDecide hof (hpend1 p) (Set.mem_singleton p) hn1
      simpa using this
    have hbU : I.Bivalent U (Xm (m + 1)) :=
      bivalent_of_canDecide_not (hpv1.mono (by simpa using hpU)) (hn2.mono (by simpa using hU''sub))
    have hnbU'' : ¬ I.CanDecide U'' (Xm (m + 1)) v := fun h => by
      have h1 := hmin _ U'' hrb1 hbU hU''sub (bivalent_of_canDecide_not h hn2)
      have h2 := Finset.card_erase_of_mem hp
      have h3 := Finset.card_pos.2 ⟨p, hp⟩
      rw [← hU''] at h2; omega
    have hqnv := hR1.canDecide_not_of_canDecide hof (hpend1 q) (by simpa using hq) hnbU''
    exact fin hrb1 hpU hqU hpv1 hqnv
  · -- the step is by a process of `U''`
    have hsU'' : β[m].proc ∈ (U'' : Set P) := by
      simp only [hU'', Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨hδU', hsp⟩
    have hn2 : ¬ I.CanDecide U'' (Xm (m + 1)) (!v) := fun h =>
      hGm.2 (CanDecide.of_step hs hsU'' hδS h)
    have hn1 : I.CanDecide {p} (Xm (m + 1)) (!v) := by
      by_contra h; exact hGm1 ⟨h, hn2⟩
    have hqv1 : I.CanDecide {q} (Xm (m + 1)) v := by
      have := hR1.canDecide_not_of_canDecide hof (hpend1 q) (by simpa using hq) hn2
      simpa using this
    exact fin hrb1 hqU hpU hqv1 hn1

end Impl

end Cslib.SharedMemory
