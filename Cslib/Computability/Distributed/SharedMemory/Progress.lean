/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Model
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.EquivFin

/-!
# Infinite executions, solo runs and progress conditions

* `Impl.exists_infExec_of_chain`: the limit of a chain of finite executions of unbounded length
  is an infinite execution.
* `Impl.WaitFree.obstructionFree`: wait-freedom implies obstruction-freedom.
* `Impl.soloOps`: run a list of operations of process `p` solo, each to completion (exists by
  obstruction-freedom), with its basic properties (`Impl.soloOps_spec`).
* `Impl.runFrom_other`: steps of other processes do not change the local state of `q`.

## Infinite executions

* `InfExec.pre e t`: the first `t` labels of `e` (`InfExec.run_pre`, `InfExec.pre_prefix`,
  `InfExec.pre_eq_take`, `InfExec.reachable_cfg`);
* `InfExec.Fair e`: every process with a pending operation eventually takes a step;
  `InfExec.first_act`: its first step is taken in its current local state;
* `InfExec.exists_good`: progress by a measure;
* `Impl.step_pend_none`, `InfExec.exists_inv_between`, `InfExec.exists_ret_between`: pending
  operations appear by invocations and disappear by responses.

## Restricted progress conditions

For a set `E` of finite executions (a usage discipline, e.g. one-shot executions or executions
with a bounded number of invocations; usually `PrefixClosed`):

* `Impl.WaitFreeOn E`, `Impl.LockFreeOn E`: wait-freedom / lock-freedom for the infinite
  executions all of whose prefixes are in `E`;
* `Impl.ObstructionFreeOn E`: a pending process running solo from a configuration reached by an
  execution of `E` returns.

They are implied by the unrestricted notions and coincide with them for `E = fun _ => True`
(`waitFreeOn_true_iff`, `lockFreeOn_true_iff`, `obstructionFreeOn_true_iff`). Wait-freedom and
lock-freedom imply obstruction-freedom (`WaitFreeOn.obstructionFreeOn`,
`LockFreeOn.obstructionFreeOn`, `LockFree.obstructionFree`), and in one-shot executions with
finitely many processes wait-freedom implies lock-freedom (`WaitFreeOn.lockFreeOn`).
-/

@[expose] public section

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-! ### Basic facts on runs -/

/-- Labels of other processes do not change the local state and pending operation of `q`. -/
lemma runFrom_other {C C' : Config A B P L} {β : List (Label P A)} (h : I.runFrom C β = some C')
    {q : P} (hq : ∀ ℓ ∈ β, ℓ.proc ≠ q) : C'.loc q = C.loc q ∧ C'.pend q = C.pend q := by
  induction β generalizing C with
  | nil => simp only [runFrom_nil, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | cons ℓ β ih =>
    simp only [runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      have h1 := step_other hs (hq ℓ (by simp))
      have h2 := ih h (fun ℓ' hℓ' => hq ℓ' (by simp [hℓ']))
      exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

lemma runFrom_eq_some_of_append {C C' : Config A B P L} {α β : List (Label P A)}
    (h : I.runFrom C (α ++ β) = some C') : ∃ C₁, I.runFrom C α = some C₁ ∧
      I.runFrom C₁ β = some C' := by
  rw [runFrom_append] at h
  cases h1 : I.runFrom C α with
  | none => simp [h1] at h
  | some C₁ => exact ⟨C₁, rfl, by simpa [h1] using h⟩

/-! ### Limits of chains of finite executions -/

/-- The limit of a chain of finite executions whose lengths are unbounded is an infinite
execution extending all of them. -/
theorem exists_infExec_of_chain (E : ℕ → List (Label P A)) (hmono : ∀ k, E k <+: E (k + 1))
    (hlen : ∀ k, k ≤ (E k).length) (hval : ∀ k, I.Valid (E k)) :
    ∃ e : I.InfExec, (∀ k n (hn : n < (E k).length), e.lbl n = (E k)[n]) ∧
      ∀ k n, n ≤ (E k).length → I.run ((E k).take n) = some (e.cfg n) := by
  have hmono' : ∀ k m, k ≤ m → E k <+: E m := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ m _ ih => exact ih.trans (hmono m)
  have hcomp : ∀ k m, E k <+: E m ∨ E m <+: E k := by
    intro k m
    rcases le_total k m with h | h
    · exact Or.inl (hmono' k m h)
    · exact Or.inr (hmono' m k h)
  -- labels
  let lbl : ℕ → Label P A := fun n => (E (n + 1))[n]'(by have := hlen (n + 1); omega)
  have hlbl : ∀ k n (hn : n < (E k).length), lbl n = (E k)[n] := by
    intro k n hn
    rcases hcomp (n + 1) k with h | h
    · exact h.getElem _
    · exact (h.getElem hn).symm
  have htake : ∀ k n, n ≤ (E k).length → (E k).take n = (List.range n).map lbl := by
    intro k n hn
    apply List.ext_getElem
    · simp; omega
    · intro j h1 h2
      simp only [List.getElem_take, List.getElem_map, List.getElem_range]
      rw [hlbl k j (by simp at h1; omega)]
  have hvalid : ∀ n, I.Valid ((List.range n).map lbl) := by
    intro n
    rw [← htake n n (hlen n)]
    exact I.valid_of_prefix (hval n) (List.take_prefix _ _)
  let cfg : ℕ → Config A B P L := fun n => (I.run ((List.range n).map lbl)).get
    (Option.isSome_iff_exists.2 (hvalid n))
  have hcfg : ∀ n, I.run ((List.range n).map lbl) = some (cfg n) := fun n => by simp [cfg]
  refine ⟨⟨cfg, lbl, ?_, ?_⟩, hlbl, ?_⟩
  · have := hcfg 0; simp at this; exact this.symm
  · intro n
    have h := hcfg (n + 1)
    rw [List.range_succ, List.map_append, List.map_singleton, run_append_of_eq I (hcfg n),
      runFrom_singleton] at h
    exact h
  · intro k n hn
    rw [htake k n hn]; exact hcfg n

/-! ### Solo runs -/

omit [DecidableEq P] [DecidableEq ι] in
lemma nextLabel_proc (C : Config A B P L) (p : P) : (I.nextLabel C p).proc = p := by
  unfold nextLabel; split <;> rfl

omit [DecidableEq ι] in
lemma nextLabel_invOf (C : Config A B P L) (p q : P) : (I.nextLabel C p).invOf q = none := by
  unfold nextLabel; split <;> rfl

lemma soloLabels_proc (p : P) (C : Config A B P L) (k : ℕ) :
    ∀ ℓ ∈ I.soloLabels p C k, ℓ.proc = p := by
  induction k generalizing C with
  | zero => simp [soloLabels]
  | succ k ih =>
    simp only [soloLabels]
    split_ifs
    · simp
    · intro ℓ hℓ
      rcases List.mem_cons.1 hℓ with rfl | hℓ
      · exact I.nextLabel_proc C p
      · exact ih _ ℓ hℓ

lemma opsOf_soloLabels (p q : P) (C : Config A B P L) (k : ℕ) :
    opsOf (I.soloLabels p C k) q = [] := by
  induction k generalizing C with
  | zero => simp [soloLabels]
  | succ k ih =>
    simp only [soloLabels]
    split_ifs
    · simp
    · simp [opsOf_cons, I.nextLabel_invOf, ih]

lemma soloLabels_succ (p : P) (C : Config A B P L) (k : ℕ) :
    I.soloLabels p C (k + 1) =
      if C.pend p = none then [] else I.nextLabel C p :: I.soloLabels p (I.soloStep p C) k := rfl

lemma soloLabels_prefix (p : P) (C : Config A B P L) (k : ℕ) :
    I.soloLabels p C k <+: I.soloLabels p C (k + 1) := by
  induction k generalizing C with
  | zero => simp [soloLabels]
  | succ k ih =>
    rw [soloLabels_succ I p C (k + 1), soloLabels_succ I p C k]
    split_ifs
    · exact List.prefix_refl _
    · exact List.cons_prefix_cons.2 ⟨rfl, ih _⟩

lemma soloLabels_length (p : P) (C : Config A B P L) (k : ℕ)
    (hk : ∀ i < k, ((I.soloStep p)^[i] C).pend p ≠ none) : (I.soloLabels p C k).length = k := by
  induction k generalizing C with
  | zero => rfl
  | succ k ih =>
    rw [soloLabels_succ, ite_eq_right (by simpa using hk 0 (by omega))]
    simp only [List.length_cons]
    rw [ih _ (fun i hi => by rw [← Function.iterate_succ_apply]; exact hk _ (by omega))]

/-- A step of `p` that keeps `p` pending is an internal step. -/
lemma eq_tau_of_step {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C')
    {p : P} (hp : ℓ.proc = p) (h1 : C.pend p ≠ none) (h2 : C'.pend p ≠ none) : ℓ = .tau p := by
  cases ℓ with
  | inv q o => simp only [Label.proc] at hp; subst hp; exact absurd (step_inv h).1 h1
  | tau q => simp only [Label.proc] at hp; subst hp; rfl
  | ret q r =>
    simp only [Label.proc] at hp; subst hp
    exact absurd (by simp [(step_ret h).2.1]) h2

/-- Wait-freedom implies obstruction-freedom. -/
theorem WaitFree.obstructionFree (hwf : I.WaitFree) : I.ObstructionFree := by
  intro C p ⟨α, hα⟩ hp
  by_contra hcon
  push Not at hcon
  let E : ℕ → List (Label P A) := fun k => α ++ I.soloLabels p C k
  have hE : ∀ k, I.run (E k) = some ((I.soloStep p)^[k] C) := fun k => by
    simp only [E]; rw [run_append_of_eq I hα, runFrom_soloLabels]
  have hElen : ∀ k, (E k).length = α.length + k := fun k => by
    simp only [E, List.length_append, I.soloLabels_length p C k (fun i _ => hcon i)]
  obtain ⟨e, hlbl, hcfg⟩ := I.exists_infExec_of_chain E
    (fun k => (List.prefix_append_right_inj α).2 (I.soloLabels_prefix p C k))
    (fun k => by rw [hElen]; omega) (fun k => ⟨_, hE k⟩)
  have hpend : ∀ m ≥ α.length, (e.cfg m).pend p ≠ none := by
    intro m hm
    have h := hcfg (m - α.length) m (by rw [hElen]; omega)
    rw [List.take_of_length_le (by rw [hElen]; omega), hE] at h
    rw [← Option.some_inj.1 h]; exact hcon _
  obtain ⟨N, hN⟩ := hwf e p α.length hpend
  apply hN (α.length + N) (by omega)
  apply I.eq_tau_of_step (e.step_eq _) _ (hpend _ (by omega)) (hpend _ (by omega))
  rw [hlbl (N + 1) (α.length + N) (by rw [hElen]; omega)]
  simp only [E]
  rw [List.getElem_append_right (by omega)]
  exact I.soloLabels_proc p C _ _ (List.getElem_mem _)

/-! ### Running operations solo to completion -/

/-- Number of solo steps `p` needs from `C` to return (`0` if it never returns). -/
noncomputable def soloTime (p : P) (C : Config A B P L) : ℕ := by
  classical
  exact if h : ∃ k, ((I.soloStep p)^[k] C).pend p = none then Nat.find h else 0

lemma soloTime_spec (p : P) (C : Config A B P L)
    (h : ∃ k, ((I.soloStep p)^[k] C).pend p = none) :
    ((I.soloStep p)^[I.soloTime p C] C).pend p = none := by
  classical
  simp only [soloTime, dite_eq_left h]
  exact Nat.find_spec h

/-- Labels of the solo execution, from `C`, of an invocation of `o` by `p` until it returns. -/
noncomputable def soloOp (p : P) (o : A.Op) (C : Config A B P L) : List (Label P A) :=
  match I.step C (.inv p o) with
  | some C₁ => .inv p o :: I.soloLabels p C₁ (I.soloTime p C₁)
  | none => []

/-- Labels of the solo execution, from `C`, of the operations `os` by `p`, one after the other,
each until it returns. -/
noncomputable def soloOps (p : P) : Config A B P L → List A.Op → List (Label P A)
  | _, [] => []
  | C, o :: os => I.soloOp p o C ++ soloOps p ((I.runFrom C (I.soloOp p o C)).getD C) os

lemma soloOp_spec (hof : I.ObstructionFree) (p : P) (o : A.Op) (ho : I.allowed p o)
    {α : List (Label P A)} {C : Config A B P L} (hα : I.run α = some C) (hC : C.pend p = none) :
    ∃ C', I.runFrom C (I.soloOp p o C) = some C' ∧ C'.pend p = none ∧
      (∀ ℓ ∈ I.soloOp p o C, ℓ.proc = p) ∧ opsOf (I.soloOp p o C) p = [o] ∧
      (respsOf (I.soloOp p o C) p).length = 1 := by
  classical
  obtain ⟨C₁, hs⟩ : ∃ C₁, I.step C (.inv p o) = some C₁ := by
    simp [step, hC, ho]
  have hC₁p : C₁.pend p ≠ none := by
    have := (step_inv hs).2.2.1; simp [this]
  have hreach : I.Reachable C₁ := ⟨α ++ [.inv p o], by
    rw [run_append_of_eq I hα, runFrom_singleton, hs]⟩
  have hfin := hof C₁ p hreach hC₁p
  have hop : I.soloOp p o C = .inv p o :: I.soloLabels p C₁ (I.soloTime p C₁) := by
    simp only [soloOp, hs]
  have hrun : I.runFrom C (I.soloOp p o C) = some ((I.soloStep p)^[I.soloTime p C₁] C₁) := by
    rw [hop, runFrom_cons, hs, Option.bind_some, runFrom_soloLabels]
  refine ⟨_, hrun, I.soloTime_spec p C₁ hfin, ?_, ?_, ?_⟩
  · rw [hop]; intro ℓ hℓ
    rcases List.mem_cons.1 hℓ with rfl | hℓ
    · rfl
    · exact I.soloLabels_proc p C₁ _ ℓ hℓ
  · rw [hop, opsOf_cons, opsOf_soloLabels]; simp
  · have := I.runFrom_counts hrun p 0 0 (Or.inl ⟨hC, rfl⟩)
    have h2 := I.soloTime_spec p C₁ hfin
    rw [hop, opsOf_cons, opsOf_soloLabels] at this
    simp only [h2, true_and, ne_eq, not_true_eq_false, false_and, or_false] at this
    rw [hop]; simpa using this.symm

theorem soloOps_spec (hof : I.ObstructionFree) (p : P) (os : List A.Op)
    (hos : ∀ o ∈ os, I.allowed p o) :
    ∀ {α : List (Label P A)} {C : Config A B P L}, I.run α = some C → C.pend p = none →
      ∃ C', I.runFrom C (I.soloOps p C os) = some C' ∧ C'.pend p = none ∧
        (∀ ℓ ∈ I.soloOps p C os, ℓ.proc = p) ∧ opsOf (I.soloOps p C os) p = os ∧
        (respsOf (I.soloOps p C os) p).length = os.length := by
  induction os with
  | nil =>
    intro α C _ hC
    exact ⟨C, rfl, hC, by simp [soloOps], by simp [soloOps], by simp [soloOps]⟩
  | cons o os ih =>
    intro α C hα hC
    obtain ⟨C₁, h1, h2, h3, h4, h5⟩ := I.soloOp_spec hof p o (hos o (by simp)) hα hC
    have hα₁ : I.run (α ++ I.soloOp p o C) = some C₁ := by rw [run_append_of_eq I hα, h1]
    obtain ⟨C₂, g1, g2, g3, g4, g5⟩ :=
      ih (fun o' ho' => hos o' (by simp [ho'])) hα₁ h2
    have hdef : I.soloOps p C (o :: os) = I.soloOp p o C ++ I.soloOps p C₁ os := by
      simp only [soloOps, h1, Option.getD_some]
    refine ⟨C₂, ?_, g2, ?_, ?_, ?_⟩
    · rw [hdef, runFrom_append_of_eq I h1, g1]
    · rw [hdef]; intro ℓ hℓ
      rcases List.mem_append.1 hℓ with hℓ | hℓ
      · exact h3 ℓ hℓ
      · exact g3 ℓ hℓ
    · rw [hdef, opsOf_append, h4, g4]; rfl
    · rw [hdef, respsOf_append, List.length_append, h5, g5]; simp; omega

end Impl

end Cslib.SharedMemory

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-! ### Prefixes of infinite executions -/

section InfExec

variable {I}

/-- The first `t` labels of an infinite execution. -/
def InfExec.pre (e : I.InfExec) (t : ℕ) : List (Label P A) :=
  (List.range t).map e.lbl

@[simp] lemma InfExec.pre_zero (e : I.InfExec) : e.pre 0 = [] := rfl

lemma InfExec.pre_succ (e : I.InfExec) (t : ℕ) : e.pre (t + 1) = e.pre t ++ [e.lbl t] := by
  simp [InfExec.pre, List.range_succ]

@[simp] lemma InfExec.length_pre (e : I.InfExec) (t : ℕ) : (e.pre t).length = t := by
  simp [InfExec.pre]

lemma InfExec.run_pre (e : I.InfExec) (t : ℕ) : I.run (e.pre t) = some (e.cfg t) := by
  induction t with
  | zero => simp [InfExec.pre, e.cfg_zero]
  | succ t ih =>
    rw [InfExec.pre_succ, run_append_of_eq I ih, runFrom_singleton, e.step_eq]

lemma InfExec.valid_pre (e : I.InfExec) (t : ℕ) : I.Valid (e.pre t) := ⟨_, e.run_pre t⟩

lemma InfExec.reachable_cfg (e : I.InfExec) (t : ℕ) : I.Reachable (e.cfg t) := ⟨_, e.run_pre t⟩

lemma InfExec.pre_prefix (e : I.InfExec) {t t' : ℕ} (h : t ≤ t') : e.pre t <+: e.pre t' := by
  induction t', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t' _ ih => rw [InfExec.pre_succ]; exact ih.trans (List.prefix_append _ _)

/-- If an infinite execution starts with the labels of `β`, its prefixes of length at most
`β.length` are prefixes of `β`. -/
lemma InfExec.pre_eq_take (e : I.InfExec) {β : List (Label P A)} {t : ℕ} (ht : t ≤ β.length)
    (h : ∀ n (hn : n < β.length), e.lbl n = β[n]) : e.pre t = β.take t := by
  apply List.ext_getElem
  · simp [InfExec.pre, ht]
  · intro n h1 h2
    simp only [InfExec.pre, List.getElem_map, List.getElem_range, List.getElem_take]
    exact h n (by simp [InfExec.pre] at h1; omega)

lemma InfExec.opsOf_pre_mono (e : I.InfExec) (p : P) {t t' : ℕ} (h : t ≤ t') :
    (opsOf (e.pre t) p).length ≤ (opsOf (e.pre t') p).length := by
  obtain ⟨γ, hγ⟩ := e.pre_prefix h
  rw [← hγ, opsOf_append, List.length_append]; omega

/-! ### Pending operations along infinite executions -/

/-- A pending operation can only disappear by a response of its process. -/
lemma step_pend_none {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C')
    {p : P} (hp : C.pend p ≠ none) (hp' : C'.pend p = none) : ∃ r, ℓ = .ret p r := by
  by_cases hq : ℓ.proc = p
  · cases ℓ with
    | inv p' o => simp only [Label.proc] at hq; subst hq; exact absurd (step_inv h).1 hp
    | tau p' =>
      simp only [Label.proc] at hq; subst hq
      rw [(step_tau h).2.1] at hp'; exact absurd hp' hp
    | ret p' r => simp only [Label.proc] at hq; subst hq; exact ⟨r, rfl⟩
  · rw [(step_other h hq).2] at hp'; exact absurd hp' hp

/-- A process that is idle at `m₁` and pending at `m₂ ≥ m₁` invoked in between. -/
lemma InfExec.exists_inv_between (e : I.InfExec) {p : P} {m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    (h₁ : (e.cfg m₁).pend p = none) (h₂ : (e.cfg m₂).pend p ≠ none) :
    ∃ t, m₁ ≤ t ∧ t < m₂ ∧ ∃ o, e.lbl t = .inv p o := by
  induction m₂, h using Nat.le_induction with
  | base => exact absurd h₁ h₂
  | succ m hle ih =>
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h₂
    rcases step_pend_some (e.step_eq m) ho with h | h
    · obtain ⟨t, ht1, ht2, o', ho'⟩ := ih (by rw [h]; simp)
      exact ⟨t, ht1, by omega, o', ho'⟩
    · exact ⟨m, hle, by omega, o, h⟩

/-- A process that is pending at `m₁` and idle at `m₂ ≥ m₁` returned in between. -/
lemma InfExec.exists_ret_between (e : I.InfExec) {p : P} {m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    (h₁ : (e.cfg m₁).pend p ≠ none) (h₂ : (e.cfg m₂).pend p = none) :
    ∃ t, m₁ ≤ t ∧ t < m₂ ∧ ∃ r, e.lbl t = .ret p r := by
  induction m₂, h using Nat.le_induction with
  | base => exact absurd h₂ h₁
  | succ m hle ih =>
    by_cases hm : (e.cfg m).pend p = none
    · obtain ⟨t, ht1, ht2, r, hr⟩ := ih hm
      exact ⟨t, ht1, by omega, r, hr⟩
    · obtain ⟨r, hr⟩ := step_pend_none (e.step_eq m) hm h₂
      exact ⟨m, hle, by omega, r, hr⟩

/-- Steps of other processes do not change the local state and pending operation of `q`. -/
lemma InfExec.cfg_add_of_proc_ne (e : I.InfExec) {t k : ℕ} {q : P}
    (h : ∀ j < k, (e.lbl (t + j)).proc ≠ q) :
    (e.cfg (t + k)).loc q = (e.cfg t).loc q ∧ (e.cfg (t + k)).pend q = (e.cfg t).pend q := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := step_other (e.step_eq (t + k)) (h k (by omega))
    rw [← Nat.add_assoc, h2.1, h2.2]
    exact h1

/-! ### Fairness and progress by a measure -/

/-- An infinite execution is *fair* if every process with a pending operation eventually takes a
step (internal step or response). -/
def InfExec.Fair (e : I.InfExec) : Prop :=
  ∀ p t, (e.cfg t).pend p ≠ none → ∃ t' ≥ t, (e.lbl t').proc = p ∧ (e.lbl t').IsStep

/-- Under fairness, a pending process eventually takes a step; its first step is taken in its
current local state. -/
lemma InfExec.first_act (e : I.InfExec) (hfair : e.Fair) {q : P} {t : ℕ}
    (hp : (e.cfg t).pend q ≠ none) :
    ∃ t' ≥ t, (e.lbl t').proc = q ∧ (e.lbl t').IsStep ∧ (e.cfg t').loc q = (e.cfg t).loc q ∧
      (e.cfg t').pend q = (e.cfg t).pend q := by
  classical
  have hex : ∃ k, (e.lbl (t + k)).proc = q := by
    obtain ⟨t₁, ht₁, hq, -⟩ := hfair q t hp
    exact ⟨t₁ - t, by rw [Nat.add_sub_cancel' ht₁]; exact hq⟩
  have hc := e.cfg_add_of_proc_ne fun j hj => Nat.find_min hex hj
  refine ⟨t + Nat.find hex, by omega, Nat.find_spec hex, ?_, hc.1, hc.2⟩
  -- the first label of `q` is not an invocation, since `q` is still pending
  have hs := e.step_eq (t + Nat.find hex)
  have hq := Nat.find_spec hex
  cases hl : e.lbl (t + Nat.find hex) with
  | inv q' o =>
    rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
    exact absurd (step_inv hs).1 (hc.2 ▸ hp)
  | ret _ _ => trivial
  | tau _ => trivial

/-- **Progress by a measure.** Let `Good` be a property of times and `μ` a measure. Suppose that
from time `t` on, as long as `Good` fails, process `p` eventually takes a step, each step of `p`
makes `Good` true or decreases `μ`, and other labels make `Good` true or do not increase `μ`.
Then `Good` eventually holds. -/
lemma InfExec.exists_good (e : I.InfExec) (p : P) (Good : ℕ → Prop) (μ : ℕ → ℕ)
    (t : ℕ)
    (hstep : ∀ t' ≥ t, ¬ Good t' → ∃ t'' ≥ t', (e.lbl t'').proc = p ∧ (e.lbl t'').IsStep)
    (hp : ∀ t' ≥ t, ¬ Good t' → (e.lbl t').proc = p → (e.lbl t').IsStep →
      Good (t' + 1) ∨ μ (t' + 1) < μ t')
    (ho : ∀ t' ≥ t, ¬ Good t' → ¬ ((e.lbl t').proc = p ∧ (e.lbl t').IsStep) →
      Good (t' + 1) ∨ μ (t' + 1) ≤ μ t') :
    ∃ t' ≥ t, Good t' := by
  induction hn : μ t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    by_contra hcon
    push Not at hcon
    obtain ⟨t'', ht'', hpt, hst⟩ := hstep t le_rfl (hcon t le_rfl)
    -- between `t` and `t''` the measure does not increase
    have hle : ∀ k, t + k ≤ t'' → μ (t + k) ≤ n := by
      intro k
      induction k with
      | zero => intro _; simp [hn]
      | succ k ihk =>
        intro hk
        have h1 := ihk (by omega)
        by_cases hpk : (e.lbl (t + k)).proc = p ∧ (e.lbl (t + k)).IsStep
        · rcases hp (t + k) (by omega) (hcon _ (by omega)) hpk.1 hpk.2 with h | h
          · exact absurd h (hcon _ (by omega))
          · rw [← Nat.add_assoc]; omega
        · rcases ho (t + k) (by omega) (hcon _ (by omega)) hpk with h | h
          · exact absurd h (hcon _ (by omega))
          · rw [← Nat.add_assoc]; omega
    have h2 := hle (t'' - t) (by omega)
    rw [show t + (t'' - t) = t'' by omega] at h2
    rcases hp t'' ht'' (hcon _ ht'') hpt hst with h | h
    · exact hcon _ (by omega) h
    · obtain ⟨t₃, ht₃, hg⟩ := ih (μ (t'' + 1)) (by omega) (t'' + 1)
        (fun t' ht' hg => hstep t' (by omega) hg)
        (fun t' ht' hg => hp t' (by omega) hg)
        (fun t' ht' hg => ho t' (by omega) hg) rfl
      exact hcon t₃ (by omega) hg

end InfExec

/-! ### Progress conditions restricted to a set of executions -/

/-- Wait-freedom for the infinite executions whose prefixes are all in `E`. -/
def WaitFreeOn (E : List (Label P A) → Prop) : Prop :=
  ∀ e : I.InfExec, (∀ t, E (e.pre t)) → ∀ (p : P) (n : ℕ),
    (∀ m ≥ n, (e.cfg m).pend p ≠ none) → ∃ N, ∀ m ≥ N, e.lbl m ≠ .tau p

/-- Lock-freedom for the infinite executions whose prefixes are all in `E`. -/
def LockFreeOn (E : List (Label P A) → Prop) : Prop :=
  ∀ e : I.InfExec, (∀ t, E (e.pre t)) → (∀ N, ∃ m ≥ N, (e.lbl m).IsStep) →
    ∀ N, ∃ m ≥ N, ∃ p r, e.lbl m = .ret p r

/-- Obstruction-freedom from the configurations reached by executions of `E`: a pending process
running solo returns. -/
def ObstructionFreeOn (E : List (Label P A) → Prop) : Prop :=
  ∀ α C p, I.run α = some C → E α → C.pend p ≠ none → ∃ k, ((I.soloStep p)^[k] C).pend p = none

variable {I}

lemma WaitFree.waitFreeOn (h : I.WaitFree) (E : List (Label P A) → Prop) : I.WaitFreeOn E :=
  fun e _ => h e

lemma LockFree.lockFreeOn (h : I.LockFree) (E : List (Label P A) → Prop) : I.LockFreeOn E :=
  fun e _ hs => h e hs

lemma ObstructionFree.obstructionFreeOn (h : I.ObstructionFree) (E : List (Label P A) → Prop) :
    I.ObstructionFreeOn E :=
  fun α _ p hα _ hp => h _ p ⟨α, hα⟩ hp

lemma waitFreeOn_true_iff : I.WaitFreeOn (fun _ => True) ↔ I.WaitFree :=
  ⟨fun h e => h e fun _ => trivial, fun h => h.waitFreeOn _⟩

lemma lockFreeOn_true_iff : I.LockFreeOn (fun _ => True) ↔ I.LockFree :=
  ⟨fun h e => h e fun _ => trivial, fun h => h.lockFreeOn _⟩

lemma obstructionFreeOn_true_iff : I.ObstructionFreeOn (fun _ => True) ↔ I.ObstructionFree :=
  ⟨fun h C p ⟨α, hα⟩ hp => h α C p hα trivial hp, fun h => h.obstructionFreeOn _⟩

lemma WaitFreeOn.mono {E E' : List (Label P A) → Prop} (h : I.WaitFreeOn E)
    (hE : ∀ α, E' α → E α) : I.WaitFreeOn E' :=
  fun e he => h e fun t => hE _ (he t)

lemma LockFreeOn.mono {E E' : List (Label P A) → Prop} (h : I.LockFreeOn E)
    (hE : ∀ α, E' α → E α) : I.LockFreeOn E' :=
  fun e he hs => h e (fun t => hE _ (he t)) hs

lemma ObstructionFreeOn.mono {E E' : List (Label P A) → Prop} (h : I.ObstructionFreeOn E)
    (hE : ∀ α, E' α → E α) : I.ObstructionFreeOn E' :=
  fun α C p hα he hp => h α C p hα (hE α he) hp

/-- A process that never returns when running solo from a reachable configuration yields an
infinite execution that continues the execution with internal steps of that process only. -/
lemma exists_infExec_solo {α : List (Label P A)} {C : Config A B P L} (hα : I.run α = some C)
    {p : P} (hp : ∀ k, ((I.soloStep p)^[k] C).pend p ≠ none) :
    ∃ e : I.InfExec, (∀ t, e.pre t = α.take t ++ List.replicate (t - α.length) (.tau p)) ∧
      (∀ m ≥ α.length, e.lbl m = .tau p) ∧ ∀ m ≥ α.length, (e.cfg m).pend p ≠ none := by
  let E : ℕ → List (Label P A) := fun k => α ++ I.soloLabels p C k
  have hE : ∀ k, I.run (E k) = some ((I.soloStep p)^[k] C) := fun k => by
    simp only [E]; rw [run_append_of_eq I hα, runFrom_soloLabels]
  have hElen : ∀ k, (E k).length = α.length + k := fun k => by
    simp only [E, List.length_append, I.soloLabels_length p C k (fun i _ => hp i)]
  obtain ⟨e, hlbl, hcfg⟩ := I.exists_infExec_of_chain E
    (fun k => (List.prefix_append_right_inj α).2 (I.soloLabels_prefix p C k))
    (fun k => by rw [hElen]; omega) (fun k => ⟨_, hE k⟩)
  have hpend : ∀ m ≥ α.length, (e.cfg m).pend p ≠ none := by
    intro m hm
    have h := hcfg (m - α.length) m (by rw [hElen]; omega)
    rw [List.take_of_length_le (by rw [hElen]; omega), hE] at h
    rw [← Option.some_inj.1 h]; exact hp _
  have htau : ∀ m ≥ α.length, e.lbl m = .tau p := by
    intro m hm
    apply I.eq_tau_of_step (e.step_eq _) _ (hpend _ hm) (hpend _ (by omega))
    rw [hlbl (m + 1 - α.length) m (by rw [hElen]; omega)]
    simp only [E]
    rw [List.getElem_append_right (by omega)]
    exact I.soloLabels_proc p C _ _ (List.getElem_mem _)
  have hpre : ∀ m (hm : m < α.length), e.lbl m = α[m] := by
    intro m hm
    rw [hlbl 0 m (by rw [hElen]; omega)]
    simp only [E, soloLabels, List.append_nil]
  refine ⟨e, fun t => ?_, htau, hpend⟩
  induction t with
  | zero => simp
  | succ t ih =>
    rw [InfExec.pre_succ, ih]
    by_cases ht : t < α.length
    · rw [hpre t ht, show t + 1 - α.length = 0 by omega, show t - α.length = 0 by omega,
        List.replicate_zero, List.append_nil, List.append_nil, List.take_add_one,
        List.getElem?_eq_getElem ht, Option.toList_some]
    · rw [htau t (by omega), List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        show t + 1 - α.length = (t - α.length) + 1 by omega, List.replicate_succ',
        List.append_assoc]

omit [DecidableEq P] in
/-- Prefixes of the infinite execution of `exists_infExec_solo` stay in `E`, if `E` is closed
under prefixes and under internal steps. -/
private lemma pre_mem_of_solo {E : List (Label P A) → Prop} (hE : PrefixClosed E)
    (htau : ∀ α p, E α → E (α ++ [.tau p])) {α : List (Label P A)} (hα : E α) (p : P) (t : ℕ) :
    E (α.take t ++ List.replicate (t - α.length) (.tau p)) := by
  induction t with
  | zero => simpa using hE.of_prefix (List.nil_prefix) hα
  | succ t ih =>
    by_cases ht : t < α.length
    · rw [show t + 1 - α.length = 0 by omega, List.replicate_zero, List.append_nil]
      exact hE.of_prefix (List.take_prefix _ _) hα
    · rw [List.take_of_length_le (by omega)] at ih ⊢
      rw [show t + 1 - α.length = (t - α.length) + 1 by omega, List.replicate_succ',
        ← List.append_assoc]
      exact htau _ p ih

/-- Wait-freedom implies obstruction-freedom on a set of executions closed under prefixes and
internal steps. -/
theorem WaitFreeOn.obstructionFreeOn {E : List (Label P A) → Prop} (h : I.WaitFreeOn E)
    (hE : PrefixClosed E) (htau : ∀ α p, E α → E (α ++ [.tau p])) : I.ObstructionFreeOn E := by
  intro α C p hα hEα hp
  by_contra hcon
  push Not at hcon
  obtain ⟨e, hpre, he, hpend⟩ := exists_infExec_solo hα hcon
  obtain ⟨N, hN⟩ := h e (fun t => hpre t ▸ pre_mem_of_solo hE htau hEα p t) p _ hpend
  exact hN (max N α.length) (le_max_left _ _) (he _ (le_max_right _ _))

/-- Lock-freedom implies obstruction-freedom on a set of executions closed under prefixes and
internal steps. -/
theorem LockFreeOn.obstructionFreeOn {E : List (Label P A) → Prop} (h : I.LockFreeOn E)
    (hE : PrefixClosed E) (htau : ∀ α p, E α → E (α ++ [.tau p])) : I.ObstructionFreeOn E := by
  intro α C p hα hEα hp
  by_contra hcon
  push Not at hcon
  obtain ⟨e, hpre, he, -⟩ := exists_infExec_solo hα hcon
  obtain ⟨m, hm, q, r, hr⟩ := h e (fun t => hpre t ▸ pre_mem_of_solo hE htau hEα p t)
    (fun N => ⟨max N α.length, le_max_left _ _, by rw [he _ (le_max_right _ _)]; trivial⟩)
    α.length
  rw [he m hm] at hr
  cases hr

/-- Lock-freedom implies obstruction-freedom. -/
theorem LockFree.obstructionFree (h : I.LockFree) : I.ObstructionFree :=
  obstructionFreeOn_true_iff.1 <|
    (lockFreeOn_true_iff.2 h).obstructionFreeOn prefixClosed_true fun _ _ _ => trivial

/-- For one-shot executions with finitely many processes, wait-freedom implies lock-freedom. -/
theorem WaitFreeOn.lockFreeOn [Finite P] {E : List (Label P A) → Prop} (h : I.WaitFreeOn E)
    (hos : ∀ α, E α → ∀ q, (opsOf α q).length ≤ 1) : I.LockFreeOn E := by
  classical
  have := Fintype.ofFinite P
  intro e hE hsteps N₀
  by_contra hret
  push Not at hret
  -- some process takes infinitely many steps
  obtain ⟨p, hp⟩ : ∃ p, ∀ N, ∃ m ≥ N, (e.lbl m).IsStep ∧ (e.lbl m).proc = p := by
    by_contra hno
    push Not at hno
    choose Nf hNf using hno
    obtain ⟨m, hm, hs⟩ := hsteps (Finset.univ.sup Nf)
    exact hNf _ m (le_trans (Finset.le_sup (Finset.mem_univ _)) hm) hs rfl
  -- hence infinitely many `tau p` (there are no responses after `N₀`)
  have htau : ∀ N, ∃ m ≥ N, e.lbl m = .tau p := by
    intro N
    obtain ⟨m, hm, hs, hpr⟩ := hp (max N N₀)
    refine ⟨m, le_of_max_le_left hm, ?_⟩
    cases hl : e.lbl m with
    | inv q o => rw [hl] at hs; exact hs.elim
    | ret q r => exact absurd hl (hret m (le_of_max_le_right hm) q r)
    | tau q => rw [hl] at hpr; simp only [Label.proc] at hpr; rw [hpr]
  obtain ⟨m₀, -, hm₀⟩ := htau 0
  have hpend₀ : (e.cfg m₀).pend p ≠ none := by
    have hs := e.step_eq m₀; rw [hm₀] at hs; exact (step_tau hs).1
  have hinv₀ : 1 ≤ (opsOf (e.pre m₀) p).length := by
    rcases I.run_counts (e.run_pre m₀) p with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact absurd h1 hpend₀
    · omega
  -- `p` stays pending forever after `m₀`
  have hpend : ∀ m ≥ m₀, (e.cfg m).pend p ≠ none := by
    intro m hm hidle
    obtain ⟨m₂, hm₂, hm₂'⟩ := htau m
    have hpend₂ : (e.cfg m₂).pend p ≠ none := by
      have hs := e.step_eq m₂; rw [hm₂'] at hs; exact (step_tau hs).1
    obtain ⟨t, ht1, -, o, ho⟩ := e.exists_inv_between hm₂ hidle hpend₂
    have hle := hos _ (hE (t + 1)) p
    rw [InfExec.pre_succ, opsOf_append, ho] at hle
    have hmono := e.opsOf_pre_mono p (hm.trans ht1)
    simp only [opsOf_cons, opsOf_nil, Label.invOf_inv, ite_true, Option.toList_some,
      List.append_nil, List.length_append, List.length_singleton] at hle
    omega
  obtain ⟨N, hN⟩ := h e hE p m₀ hpend
  obtain ⟨m, hm, hm'⟩ := htau N
  exact hN m hm hm'

end Impl

end Cslib.SharedMemory
