/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Covering

/-!
# Running processes solo to completion under restricted obstruction-freedom

`Impl.soloOp_spec` (`Progress.lean`) runs one operation solo to completion under (unrestricted)
obstruction-freedom. Here the same is done under obstruction-freedom on a set `E` of executions
(`Impl.ObstructionFreeOn E`), e.g. one-shot executions or executions with boundedly many
invocations:

* `Impl.soloOp_spec_of_obstructionFreeOn` — an invocation of `o` by an idle process `p`, run solo,
  returns;
* `Impl.exists_finish` — the processes of a list can finish their pending operations one after the
  other, without invoking anything, while the other processes do not move.

Also: solo steps preserve reachability (`Impl.Reachable.soloStep`,
`Impl.Reachable.iterate_soloStep`).
-/

@[expose] public section

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

variable {I} in
/-- A solo step from a reachable configuration leads to a reachable configuration. -/
lemma Reachable.soloStep {C : Config A B P L} (h : I.Reachable C) (p : P) :
    I.Reachable (I.soloStep p C) := by
  obtain ⟨α, hα⟩ := h
  exact ⟨α ++ I.soloLabels p C 1, by rw [run_append_of_eq I hα, runFrom_soloLabels]; rfl⟩

variable {I} in
/-- Solo runs from a reachable configuration lead to reachable configurations. -/
lemma Reachable.iterate_soloStep {C : Config A B P L} (h : I.Reachable C) (p : P) (k : ℕ) :
    I.Reachable ((I.soloStep p)^[k] C) := by
  obtain ⟨α, hα⟩ := h
  exact ⟨α ++ I.soloLabels p C k, by rw [run_append_of_eq I hα, runFrom_soloLabels]⟩

/-- **Running one operation solo**, under obstruction-freedom on `E`: if `p` is idle after `α`
and `α` followed by the invocation of `o` is in `E`, then `p` completes `o` solo. -/
lemma soloOp_spec_of_obstructionFreeOn {E : List (Label P A) → Prop}
    (hof : I.ObstructionFreeOn E) (p : P) (o : A.Op) (ho : I.allowed p o)
    {α : List (Label P A)} {C : Config A B P L} (hα : I.run α = some C) (hC : C.pend p = none)
    (hE : E (α ++ [.inv p o])) :
    ∃ C', I.runFrom C (I.soloOp p o C) = some C' ∧ C'.pend p = none ∧
      (∀ ℓ ∈ I.soloOp p o C, ℓ.proc = p) ∧ opsOf (I.soloOp p o C) p = [o] ∧
      (respsOf (I.soloOp p o C) p).length = 1 := by
  obtain ⟨C₁, hs⟩ : ∃ C₁, I.step C (.inv p o) = some C₁ := by
    simp [step, hC, ho]
  have hC₁p : C₁.pend p ≠ none := by
    have := (step_inv hs).2.2.1; simp [this]
  have hfin := hof _ C₁ p (by rw [run_append_of_eq I hα, runFrom_singleton, hs]) hE hC₁p
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

/-- **Finishing pending operations by solo runs.** Under obstruction-freedom on a set `E` of
executions that is closed under appending fragments without invocations, from a configuration
reached by an execution of `E` the processes of `ps` can finish their pending operations one
after the other: the fragment `γ` consists of steps of `ps` only, invokes nothing, and does not
move the other processes. -/
theorem exists_finish {E : List (Label P A) → Prop} (hof : I.ObstructionFreeOn E)
    (hE : ∀ α β, E α → (∀ q, opsOf β q = []) → E (α ++ β)) (ps : List P) :
    ∀ {α : List (Label P A)} {F : Config A B P L}, I.run α = some F → E α →
      ∃ γ F', (∀ ℓ ∈ γ, ℓ.proc ∈ ps) ∧ (∀ q, opsOf γ q = []) ∧ I.runFrom F γ = some F' ∧
        (∀ p ∈ ps, F'.pend p = none) ∧
        (∀ q, q ∉ ps → F'.loc q = F.loc q ∧ F'.pend q = F.pend q) := by
  induction ps with
  | nil =>
    intro α F _ _
    exact ⟨[], F, by simp, by simp, rfl, by simp, fun _ _ => ⟨rfl, rfl⟩⟩
  | cons p ps ih =>
    intro α F hα hEα
    have hfin : ∃ K, ((I.soloStep p)^[K] F).pend p = none := by
      by_cases hp : F.pend p = none
      · exact ⟨0, hp⟩
      · exact hof α F p hα hEα hp
    set γ₁ := I.soloLabels p F (I.soloTime p F)
    set F₁ := (I.soloStep p)^[I.soloTime p F] F
    have hr₁ : I.runFrom F γ₁ = some F₁ := I.runFrom_soloLabels p F _
    have hF₁ : F₁.pend p = none := I.soloTime_spec p F hfin
    have hops₁ : ∀ q, opsOf γ₁ q = [] := fun q => I.opsOf_soloLabels p q F _
    obtain ⟨γ, F', hγ, hops, hr, hfin', hoth⟩ := ih (α := α ++ γ₁) (F := F₁)
      (by rw [run_append_of_eq I hα, hr₁]) (hE _ _ hEα hops₁)
    refine ⟨γ₁ ++ γ, F', fun ℓ hℓ => ?_, fun q => by simp [hops₁ q, hops q],
      by rw [runFrom_append_of_eq I hr₁, hr], fun q hq => ?_, fun q hq => ?_⟩
    · rcases List.mem_append.1 hℓ with h | h
      · rw [I.soloLabels_proc p F _ ℓ h]; simp
      · exact List.mem_cons_of_mem _ (hγ ℓ h)
    · rcases List.mem_cons.1 hq with rfl | hq
      · by_cases hq' : q ∈ ps
        · exact hfin' q hq'
        · rw [(hoth q hq').2, hF₁]
      · exact hfin' q hq
    · have hqp : q ≠ p := fun h => hq (by simp [h])
      have hqs : q ∉ ps := fun h => hq (List.mem_cons_of_mem _ h)
      rw [(hoth q hqs).1, (hoth q hqs).2, (I.iterate_soloStep_other hqp F _).1,
        (I.iterate_soloStep_other hqp F _).2]
      exact ⟨rfl, rfl⟩

end Impl

end Cslib.SharedMemory
