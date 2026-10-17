/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Progress
public import Cslib.Foundations.Data.Nat.Descent

/-!
# Wait-freedom and lock-freedom from potentials

Termination arguments by a natural-number potential that decreases with the steps of a process.

* `Impl.countP_isTauOf_add_le_of_cfgPotential` (quantitative, finite executions): along an
  execution fragment in which `p` stays pending, if a potential `Ψ` on configurations never
  increases and strictly decreases at every internal step of `p`, then the number of internal
  steps of `p` is at most the drop of `Ψ`. Corollary for a potential on local states:
  `Impl.tauSteps_le_of_potential` (step complexity); `Impl.tauSteps_le_potential_invoke` bounds
  the accesses of a whole operation by the potential of the local state right after its
  invocation.
* `Impl.waitFreeOn_of_runPotential` (infinite executions): the same hypothesis for the steps of
  the executions of a set `E` gives wait-freedom on `E` (the potential may depend on the
  execution); `Impl.waitFreeOn_of_cfgPotential` for a potential on configurations. Corollaries:
  `Impl.waitFree_of_cfgPotential` (potential and invariant on configurations) and
  `Impl.waitFree_of_potential` (potential on local states: each operation finishes within
  `μ p l` own steps).
* `Impl.lockFreeOn_of_potential`, `Impl.lockFree_of_potential`: a global potential that decreases
  at every non-response step gives lock-freedom.
* `Impl.InfExec.exists_act_of_pending`: under fairness, a process that is pending forever acts
  infinitely often; `Impl.InfExec.false_of_descent`: a measure that never increases from some
  time on and strictly decreases at every action of a process that is pending forever gives a
  contradiction (under fairness), the usual termination argument for a process stuck in a loop.

The local potential condition is turned into the configuration one by
`Impl.potential_step_of_local`, based on `Impl.step_tau_or_other` (a step taken while `p` stays
pending is an internal step of `p` or does not change `p`'s local state).
-/

@[expose] public section

namespace Cslib.SharedMemory

namespace Impl

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
  (I : Impl A B P L)

/-- A step taken while `p` is pending before and after it is an internal step of `p` or a step
of another process (which does not change the local state of `p`). -/
lemma step_tau_or_other {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C')
    {p : P} (hp : C.pend p ≠ none) (hp' : C'.pend p ≠ none) :
    ℓ = .tau p ∨ (ℓ.proc ≠ p ∧ C'.loc p = C.loc p) := by
  by_cases hq : ℓ.proc = p
  · cases ℓ with
    | inv q o =>
      simp only [Label.proc] at hq; subst hq
      exact absurd (step_inv h).1 hp
    | ret q r =>
      simp only [Label.proc] at hq; subst hq
      exact absurd (by simp [(step_ret h).2.1]) hp'
    | tau q => simp only [Label.proc] at hq; exact Or.inl (hq ▸ rfl)
  · exact Or.inr ⟨hq, (step_other h hq).1⟩

/-- A potential on local states that decreases at every base-object access of a process does
not increase at the steps taken while the process stays pending, and decreases at its internal
steps. -/
lemma potential_step_of_local (μ : P → L → ℕ)
    (hμ : ∀ p l i o k, I.act p l = .access i o k → ∀ x, μ p (k x) < μ p l)
    {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C') {p : P}
    (hp : C.pend p ≠ none) (hp' : C'.pend p ≠ none) :
    μ p (C'.loc p) ≤ μ p (C.loc p) ∧ (ℓ = .tau p → μ p (C'.loc p) < μ p (C.loc p)) := by
  rcases I.step_tau_or_other h hp hp' with rfl | ⟨hq, hloc⟩
  · obtain ⟨-, -, i, o, k, hact, -, hloc⟩ := step_tau h
    have : μ p (C'.loc p) < μ p (C.loc p) := by
      simp only [hloc, Function.update_self]
      exact hμ _ _ i o k hact _
    exact ⟨this.le, fun _ => this⟩
  · rw [hloc]
    exact ⟨le_rfl, fun h' => absurd (by rw [h']; rfl) hq⟩

/-! ### Finite executions -/

/-- **Step complexity from a potential on configurations.** Along an execution fragment `γ` from
`C` to `C'` in which `p` is pending at the start and does not return, if every step of the
fragment (taken while `p` is pending) does not increase `Ψ` and every internal step of `p`
decreases it, then the number of internal steps of `p` in `γ` is at most `Ψ C - Ψ C'`. -/
theorem countP_isTauOf_add_le_of_cfgPotential (p : P) (Ψ : Config A B P L → ℕ) :
    ∀ (γ : List (Label P A)) (C C' : Config A B P L), I.runFrom C γ = some C' →
      C.pend p ≠ none → (∀ r, .ret p r ∉ γ) →
      (∀ β ℓ D D', β ++ [ℓ] <+: γ → I.runFrom C β = some D → I.step D ℓ = some D' →
        D.pend p ≠ none → D'.pend p ≠ none → Ψ D' ≤ Ψ D ∧ (ℓ = .tau p → Ψ D' < Ψ D)) →
      γ.countP (Label.isTauOf p) + Ψ C' ≤ Ψ C
  | [], C, C', h, _, _, _ => by
    simp only [runFrom_nil, Option.some.injEq] at h; subst h; simp
  | ℓ :: γ, C, C', h, hp, hr, hΨ => by
    simp only [runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      have hp₁ : C₁.pend p ≠ none := by
        by_cases hq : ℓ.proc = p
        · cases ℓ with
          | inv q o =>
            simp only [Label.proc] at hq; subst hq; exact absurd (step_inv hs).1 hp
          | ret q r =>
            simp only [Label.proc] at hq; subst hq; exact absurd List.mem_cons_self (hr r)
          | tau q => rw [(step_tau hs).2.1]; exact hp
        · rw [(step_other hs hq).2]; exact hp
      have h1 := hΨ [] ℓ C C₁ (by simp) rfl hs hp hp₁
      have ih := countP_isTauOf_add_le_of_cfgPotential p Ψ γ C₁ C' h hp₁
        (fun r hr' => hr r (List.mem_cons_of_mem _ hr'))
        (fun β ℓ' D D' hβ hD hs' hD₁ hD₂ => hΨ (ℓ :: β) ℓ' D D'
          (by simpa using hβ) (by simpa [runFrom_cons, hs] using hD) hs' hD₁ hD₂)
      rw [List.countP_cons]
      by_cases ht : ℓ = .tau p
      · have := h1.2 ht; subst ht; simp; omega
      · have : ℓ.isTauOf p = false := by
          cases h' : ℓ.isTauOf p
          · rfl
          · exact absurd (Label.isTauOf_eq_true_iff.1 h') ht
        simp only [this, Bool.false_eq_true, ↓reduceIte]; omega

/-- **Step complexity from a potential on local states.** If a potential on local states strictly
decreases at every base-object access, then along any execution fragment in which `p` stays
pending (no response of `p`), the number of accesses of `p` is at most the drop of its
potential. -/
theorem tauSteps_le_of_potential (μ : P → L → ℕ)
    (hμ : ∀ p l i o k, I.act p l = .access i o k → ∀ x, μ p (k x) < μ p l) (p : P)
    (γ : List (Label P A)) (C C' : Config A B P L) (h : I.runFrom C γ = some C')
    (hp : C.pend p ≠ none) (hr : ∀ r, .ret p r ∉ γ) :
    γ.countP (Label.isTauOf p) + μ p (C'.loc p) ≤ μ p (C.loc p) :=
  I.countP_isTauOf_add_le_of_cfgPotential p (fun C => μ p (C.loc p)) γ C C' h hp hr
    fun _ _ _ _ _ _ hs hD hD' => I.potential_step_of_local μ hμ hs hD hD'

/-- **Step complexity of an operation from a potential on local states.** If a potential on local
states strictly decreases at every base-object access, then after `p` invokes `o` (in some local
state `l`), `p` performs at most `μ p (I.invoke p l o)` base-object accesses before it returns
(`γ` is any continuation not containing a response of `p`). -/
theorem tauSteps_le_potential_invoke (μ : P → L → ℕ)
    (hμ : ∀ p l i o k, I.act p l = .access i o k → ∀ x, μ p (k x) < μ p l)
    {α γ : List (Label P A)} {p : P} {o : A.Op} (hv : I.Valid (α ++ .inv p o :: γ))
    (hret : ∀ r, .ret p r ∉ γ) : ∃ l, γ.countP (Label.isTauOf p) ≤ μ p (I.invoke p l o) := by
  obtain ⟨C', h⟩ := hv
  rw [run, runFrom_append] at h
  cases hα : I.runFrom I.initCfg α with
  | none => simp [hα] at h
  | some C₀ =>
    simp only [hα, Option.bind_some, runFrom_cons] at h
    cases hs : I.step C₀ (.inv p o) with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨-, -, hpend, hloc, -⟩ := step_inv hs
      have := I.tauSteps_le_of_potential μ hμ p γ C₁ C' h (by simp [hpend]) hret
      rw [hloc, Function.update_self] at this
      exact ⟨C₀.loc p, by omega⟩

/-! ### Infinite executions -/

/-- **Wait-freedom from a potential on executions**, restricted to the executions of `E`.
Suppose that at every step `C → C'` extending an execution `α` (with `α ++ [ℓ] ∈ E`) and taken
while `p` stays pending, the potential `Ψ p` of the execution and its final configuration does not
increase, and that it strictly decreases at the internal steps of `p`. Then the implementation is
wait-free on `E`. (The potential may depend on the execution, e.g. through ghost state.) -/
theorem waitFreeOn_of_runPotential {E : List (Label P A) → Prop}
    (Ψ : P → List (Label P A) → Config A B P L → ℕ)
    (hΨ : ∀ p α C ℓ C', I.run α = some C → E (α ++ [ℓ]) → I.step C ℓ = some C' →
      C.pend p ≠ none → C'.pend p ≠ none →
        Ψ p (α ++ [ℓ]) C' ≤ Ψ p α C ∧ (ℓ = .tau p → Ψ p (α ++ [ℓ]) C' < Ψ p α C)) :
    I.WaitFreeOn E := by
  intro e hE p n hpend
  have hstep : ∀ m ≥ n, Ψ p (e.pre (m + 1)) (e.cfg (m + 1)) ≤ Ψ p (e.pre m) (e.cfg m) ∧
      (e.lbl m = .tau p →
        Ψ p (e.pre (m + 1)) (e.cfg (m + 1)) < Ψ p (e.pre m) (e.cfg m)) := fun m hm => by
    rw [e.pre_succ m]
    exact hΨ p _ _ _ _ (e.run_pre m) (e.pre_succ m ▸ hE (m + 1)) (e.step_eq m) (hpend m hm)
      (hpend (m + 1) (by omega))
  obtain ⟨T, -, hT⟩ := Nat.eventually_not_of_succ_le (f := fun m => Ψ p (e.pre m) (e.cfg m))
    (fun m hm => (hstep m hm).1)
    (p := fun m => e.lbl m = .tau p) fun m hm => (hstep m hm).2
  exact ⟨T, hT⟩

/-- **Wait-freedom from a potential on configurations**, restricted to the executions of `E`.
Suppose that at every step `C → C'` extending an execution `α` (with `α ++ [ℓ] ∈ E`) and taken
while `p` stays pending, the potential `Ψ p` does not increase, and that it strictly decreases at
the internal steps of `p`. Then the implementation is wait-free on `E`. -/
theorem waitFreeOn_of_cfgPotential {E : List (Label P A) → Prop} (Ψ : P → Config A B P L → ℕ)
    (hΨ : ∀ p α C ℓ C', I.run α = some C → E (α ++ [ℓ]) → I.step C ℓ = some C' →
      C.pend p ≠ none → C'.pend p ≠ none → Ψ p C' ≤ Ψ p C ∧ (ℓ = .tau p → Ψ p C' < Ψ p C)) :
    I.WaitFreeOn E :=
  I.waitFreeOn_of_runPotential (fun p _ C => Ψ p C) hΨ

/-- **Wait-freedom from a potential on configurations.** If an invariant `Inv` holds initially and
is preserved by steps, and the potential `Ψ p` never increases at steps taken while `p` is
pending and strictly decreases at the internal steps of `p`, then the implementation is
wait-free. -/
theorem waitFree_of_cfgPotential (Inv : Config A B P L → Prop) (hinit : Inv I.initCfg)
    (hstep : ∀ C C' ℓ, Inv C → I.step C ℓ = some C' → Inv C')
    (Ψ : P → Config A B P L → ℕ)
    (hΨ : ∀ p C C' ℓ, Inv C → C.pend p ≠ none → I.step C ℓ = some C' →
      Ψ p C' ≤ Ψ p C ∧ (ℓ = .tau p → Ψ p C' < Ψ p C)) : I.WaitFree :=
  waitFreeOn_true_iff.1 <| I.waitFreeOn_of_cfgPotential Ψ fun p _ C ℓ _ hα _ hs hp _ =>
    hΨ p C _ ℓ (invariant_of_run hinit (fun C ℓ C' hC hs => hstep C C' ℓ hC hs) hα) hp hs

/-- **Bounded steps ⇒ wait-free.** If a potential on local states strictly decreases at every
base-object access of a process, the implementation is wait-free (each operation finishes within
`μ p l` own steps). -/
theorem waitFree_of_potential (μ : P → L → ℕ)
    (hμ : ∀ p l i o k, I.act p l = .access i o k → ∀ x, μ p (k x) < μ p l) : I.WaitFree :=
  waitFreeOn_true_iff.1 <| I.waitFreeOn_of_cfgPotential (fun p C => μ p (C.loc p))
    fun _ _ _ _ _ _ _ hs hp hp' => I.potential_step_of_local μ hμ hs hp hp'

/-- **Lock-freedom from a potential**, restricted to the executions of `E`: if every step that is
not a response, extending an execution `α` with `α ++ [ℓ] ∈ E`, strictly decreases a potential on
configurations, then every infinite execution of `E` has infinitely many responses. -/
theorem lockFreeOn_of_potential {E : List (Label P A) → Prop} (pot : Config A B P L → ℕ)
    (h : ∀ α C ℓ C', I.run α = some C → E (α ++ [ℓ]) → I.step C ℓ = some C' →
      (∀ p r, ℓ ≠ .ret p r) → pot C' < pot C) : I.LockFreeOn E := by
  intro e hE _ N
  by_contra hcon
  push Not at hcon
  have hlt : ∀ m ≥ N, pot (e.cfg (m + 1)) < pot (e.cfg m) := fun m hm =>
    h _ _ _ _ (e.run_pre m) (e.pre_succ m ▸ hE (m + 1)) (e.step_eq m) (hcon m hm)
  obtain ⟨T, hT, hc⟩ := Nat.eventually_not_of_succ_le (f := fun m => pot (e.cfg m))
    (fun m hm => (hlt m hm).le)
    (p := fun _ => True) fun m hm _ => hlt m hm
  exact hc T le_rfl trivial

/-- **Lock-freedom from a potential**: if every step that is not a response strictly decreases a
potential on reachable configurations, the implementation is lock-free. -/
theorem lockFree_of_potential (pot : Config A B P L → ℕ)
    (h : ∀ α C ℓ C', I.run α = some C → I.step C ℓ = some C' → (∀ p r, ℓ ≠ .ret p r) →
      pot C' < pot C) : I.LockFree :=
  lockFreeOn_true_iff.1 <|
    I.lockFreeOn_of_potential pot fun α C ℓ C' hα _ hs hr => h α C ℓ C' hα hs hr

/-! ### Processes pending forever in fair executions -/

section PendingForever

variable {I}

/-- Under fairness, a process that is pending from time `T` on acts at some time `≥ t`, for every
`t ≥ T`. -/
theorem InfExec.exists_act_of_pending (e : I.InfExec) (hfair : e.Fair) {q : P} {T : ℕ}
    (hp : ∀ t ≥ T, (e.cfg t).pend q ≠ none) (t : ℕ) (ht : T ≤ t) :
    ∃ t' ≥ t, (e.lbl t').proc = q := by
  obtain ⟨t', h1, h2, -⟩ := e.first_act hfair (hp t ht)
  exact ⟨t', h1, h2⟩

/-- Under fairness, no process `q` can be pending from time `t₀` on if some measure `μ` of times
does not increase from `t₀` on and strictly decreases at every action of `q`. -/
theorem InfExec.false_of_descent (e : I.InfExec) (hfair : e.Fair) (q : P) (t₀ : ℕ) (μ : ℕ → ℕ)
    (hp : ∀ t ≥ t₀, (e.cfg t).pend q ≠ none)
    (hle : ∀ t ≥ t₀, (e.lbl t).proc ≠ q → μ (t + 1) ≤ μ t)
    (hlt : ∀ t ≥ t₀, (e.lbl t).proc = q → μ (t + 1) < μ t) : False := by
  have hmono : ∀ t ≥ t₀, μ (t + 1) ≤ μ t := fun t ht => by
    by_cases h : (e.lbl t).proc = q
    · exact (hlt t ht h).le
    · exact hle t ht h
  obtain ⟨T, hT, hc⟩ := Nat.eventually_not_of_succ_le hmono hlt
  obtain ⟨t', ht', hq⟩ := e.exists_act_of_pending hfair hp T hT
  exact hc t' ht' hq

end PendingForever

end Impl

end Cslib.SharedMemory
