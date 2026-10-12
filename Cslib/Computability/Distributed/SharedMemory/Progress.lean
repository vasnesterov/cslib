/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Model

/-!
# Infinite executions, solo runs and progress conditions

* `Impl.exists_infExec_of_chain`: the limit of a chain of finite executions of unbounded length
  is an infinite execution.
* `Impl.WaitFree.obstructionFree`: wait-freedom implies obstruction-freedom.
* `Impl.soloOps`: run a list of operations of process `p` solo, each to completion (exists by
  obstruction-freedom), with its basic properties (`Impl.soloOps_spec`).
* `Impl.runFrom_other`: steps of other processes do not change the local state of `q`.

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
