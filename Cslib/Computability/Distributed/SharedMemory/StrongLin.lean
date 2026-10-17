/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Progress
public import Cslib.Computability.Distributed.SharedMemory.LinPoints

/-!
# Strong linearizability

Strong linearizability (Golab, Higham and Woelfel, STOC 2011) for implementations in the
asynchronous shared-memory model (`Cslib.SharedMemory.Impl`).

An implementation is *strongly linearizable* if there is a linearization function `h` (mapping
every finite execution to a linearization of it) that is *prefix-closed*: if `α` is a prefix of
`β` then `h α` is a prefix of `h β`. Executions are label lists; since processes and base objects
are deterministic, a label list determines the whole execution (including the internal steps),
so `h` may depend on the internal steps, as in the original definition.

* `Impl.IsStrongLinFun`, `Impl.StronglyLinearizable` — for deterministic sequential
  specifications (`ObjSpec`, linearizations as in `IsLinearization`).
* `Impl.NStronglyLinearizable S` — for *nondeterministic* sequential specifications
  (`NSpec`, `IsNLinearization`).
  For a deterministic specification the two notions agree
  (`Impl.nStronglyLinearizable_toNSpec_iff`).
* `Impl.LinSim`, `Impl.stronglyLinearizable_of_linSim` — a *forward simulation* into the atomic
  object (whose states are linearizations, and whose steps append operations) yields strong
  linearizability (Attiya–Enea, DISC 2019). Every step of the implementation may linearize any
  number of operations (linearization points, helping).

## Restriction to a class of executions

Objects with a *usage discipline* (one-shot objects, objects whose operations may only be invoked
by designated processes, objects that may be used only after some event) need correctness only
on the executions that respect the discipline. For a set `E` of finite executions (intended to be
`PrefixClosed`):

* `Impl.StrongLinOn E`: a linearization function on the executions of `E`, prefix-closed
  within `E`;
* `Impl.NStrongLinOn S E`: the same for a nondeterministic specification `S`.

Each is implied by its unrestricted version (and equivalent to it for `E = fun _ => True`), so
impossibility results proved for the restricted notions are stronger. The corresponding
restricted progress conditions `Impl.WaitFreeOn`, `Impl.LockFreeOn`, `Impl.ObstructionFreeOn`
are in `Progress.lean`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

/-! ## Strong linearizability (deterministic specifications) -/

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-- A *strong linearization function* (Golab–Higham–Woelfel): a linearization function that is
prefix-closed on executions. -/
def IsStrongLinFun (h : List (Label P A) → List (OpId P × A.Op)) : Prop :=
  I.IsLinFun h ∧ ∀ α β, I.Valid β → α <+: β → h α <+: h β

/-- The implementation is *strongly linearizable*. -/
def StronglyLinearizable : Prop := ∃ h, I.IsStrongLinFun h

theorem StronglyLinearizable.linearizable {I : Impl A B P L} (h : I.StronglyLinearizable) :
    I.Linearizable := by
  obtain ⟨f, hf, -⟩ := h; exact ⟨f, hf⟩

/-! ### Forward simulations -/

/-- A *forward simulation* of the implementation by the atomic object whose states are
linearizations (Attiya–Enea): `R α C L` relates an execution `α` with final configuration `C`
to a linearization `L`; every step extends the linearization by zero or more operations. -/
structure LinSim (R : List (Label P A) → Config A B P L → List (OpId P × A.Op) → Prop) :
    Prop where
  init : R [] I.initCfg []
  step : ∀ α C L ℓ C', I.run α = some C → R α C L → I.step C ℓ = some C' →
    ∃ L', R (α ++ [ℓ]) C' (L ++ L')
  lin : ∀ α C L, I.run α = some C → R α C L → IsLinearization α L

section Sim

variable (R : List (Label P A) → Config A B P L → List (OpId P × A.Op) → Prop)

/-- One step of the canonical linearization function of a simulation. -/
noncomputable def simExt (α : List (Label P A)) (ℓ : Label P A) (L : List (OpId P × A.Op)) :
    List (OpId P × A.Op) := by
  classical
  exact if h : ∃ L', ∀ C C', I.run α = some C → I.step C ℓ = some C' →
      R (α ++ [ℓ]) C' (L ++ L') then L ++ h.choose else L

/-- The canonical linearization function of a simulation, on reversed executions. -/
noncomputable def simLinRev : List (Label P A) → List (OpId P × A.Op)
  | [] => []
  | ℓ :: rα => I.simExt R rα.reverse ℓ (simLinRev rα)

/-- The canonical linearization function of a simulation. -/
noncomputable def simLin (α : List (Label P A)) : List (OpId P × A.Op) :=
  I.simLinRev R α.reverse

lemma simLin_append_singleton (α : List (Label P A)) (ℓ : Label P A) :
    I.simLin R (α ++ [ℓ]) = I.simExt R α ℓ (I.simLin R α) := by
  simp [simLin, simLinRev]

lemma simLin_prefix_singleton (α : List (Label P A)) (ℓ : Label P A) :
    I.simLin R α <+: I.simLin R (α ++ [ℓ]) := by
  rw [simLin_append_singleton, simExt]
  split_ifs
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

lemma simLin_prefix (α β : List (Label P A)) : I.simLin R α <+: I.simLin R (α ++ β) := by
  induction β using List.reverseRecOn with
  | nil => simp
  | append_singleton β ℓ ih =>
    rw [← List.append_assoc]
    exact ih.trans (I.simLin_prefix_singleton R _ ℓ)

lemma simLin_spec (hR : I.LinSim R) (α : List (Label P A)) (C : Config A B P L)
    (h : I.run α = some C) : R α C (I.simLin R α) := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simp only [run_nil, Option.some.injEq] at h; subst h; exact hR.init
  | append_singleton α ℓ ih =>
    rw [run, runFrom_append] at h
    cases hα : I.runFrom I.initCfg α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some, runFrom_singleton] at h
      have hR0 := ih C₀ hα
      obtain ⟨L', hL'⟩ := hR.step α C₀ _ ℓ C hα hR0 h
      have hex : ∃ L', ∀ C₁ C₁', I.run α = some C₁ → I.step C₁ ℓ = some C₁' →
          R (α ++ [ℓ]) C₁' (I.simLin R α ++ L') := by
        refine ⟨L', fun C₁ C₁' h1 h2 => ?_⟩
        have e1 : C₁ = C₀ := by rw [run] at h1; rw [hα] at h1; exact (Option.some.inj h1).symm
        subst e1
        rw [h] at h2; cases h2; exact hL'
      rw [simLin_append_singleton, simExt]
      classical
      rw [dite_eq_left_of_eq_true (eq_true hex)]
      exact hex.choose_spec C₀ C hα h

/-- **Forward simulation ⇒ strong linearizability.** -/
theorem stronglyLinearizable_of_linSim (hR : I.LinSim R) : I.StronglyLinearizable := by
  refine ⟨I.simLin R, fun α ⟨C, hC⟩ => hR.lin α C _ hC (I.simLin_spec R hR α C hC), ?_⟩
  rintro α β - ⟨γ, rfl⟩
  exact I.simLin_prefix R α γ

end Sim

end Impl

section NLin

variable [DecidableEq P]

namespace Impl

variable [DecidableEq ι] (I : Impl A B P L)

/-- Strong linearizability with respect to a nondeterministic specification `S`. -/
def NStronglyLinearizable (S : NSpec A.Op A.Resp) : Prop :=
  ∃ h : List (Label P A) → List (OpId P × A.Op × A.Resp),
    (∀ α, I.Valid α → IsNLinearization S α (h α)) ∧ ∀ α β, I.Valid β → α <+: β → h α <+: h β

/-- For deterministic specifications, strong linearizability implies strong linearizability
with respect to the specification viewed as a nondeterministic one. -/
theorem StronglyLinearizable.nStronglyLinearizable {I : Impl A B P L}
    (h : I.StronglyLinearizable) : I.NStronglyLinearizable A.toNSpec := by
  obtain ⟨f, hf, hpre⟩ := h
  refine ⟨fun α => A.annotate A.init (f α), fun α hα => (hf α hα).isNLinearization_annotate, ?_⟩
  intro α β hβ hαβ
  obtain ⟨M, hM⟩ := hpre α β hβ hαβ
  change A.annotate A.init (f α) <+: A.annotate A.init (f β)
  rw [← hM, ObjSpec.annotate_append]
  exact List.prefix_append _ _

/-- For deterministic specifications, strong linearizability is strong linearizability with
respect to the specification viewed as a nondeterministic one. -/
theorem nStronglyLinearizable_toNSpec_iff {I : Impl A B P L} :
    I.NStronglyLinearizable A.toNSpec ↔ I.StronglyLinearizable := by
  refine ⟨fun ⟨f, hf, hpre⟩ => ⟨fun α => (f α).map fun y => (y.1, y.2.1),
    fun α hα => (hf α hα).isLinearization_map, fun α β hβ hαβ => ?_⟩,
    StronglyLinearizable.nStronglyLinearizable⟩
  obtain ⟨M, hM⟩ := hpre α β hβ hαβ
  exact ⟨M.map fun y => (y.1, y.2.1), by simp only [← hM, List.map_append]⟩

end Impl

end NLin

end Cslib.SharedMemory

/-! ## Strong linearizability restricted to a class of executions -/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-- Strong linearizability on the executions of `E`. -/
def StrongLinOn (E : List (Label P A) → Prop) : Prop :=
  ∃ h : List (Label P A) → List (OpId P × A.Op),
    (∀ α, I.Valid α → E α → IsLinearization α (h α)) ∧
    ∀ α β, I.Valid β → E β → α <+: β → h α <+: h β

/-- Strong linearizability with respect to a nondeterministic specification, on the executions
of `E`. -/
def NStrongLinOn (S : NSpec A.Op A.Resp) (E : List (Label P A) → Prop) : Prop :=
  ∃ h : List (Label P A) → List (OpId P × A.Op × A.Resp),
    (∀ α, I.Valid α → E α → IsNLinearization S α (h α)) ∧
    ∀ α β, I.Valid β → E β → α <+: β → h α <+: h β

variable {I}

lemma StronglyLinearizable.strongLinOn (h : I.StronglyLinearizable) (E : List (Label P A) → Prop) :
    I.StrongLinOn E := by
  obtain ⟨f, hf, hp⟩ := h
  exact ⟨f, fun α hα _ => hf α hα, fun α β hβ _ hαβ => hp α β hβ hαβ⟩

lemma NStronglyLinearizable.nStrongLinOn {S : NSpec A.Op A.Resp} (h : I.NStronglyLinearizable S)
    (E : List (Label P A) → Prop) : I.NStrongLinOn S E := by
  obtain ⟨f, hf, hp⟩ := h
  exact ⟨f, fun α hα _ => hf α hα, fun α β hβ _ hαβ => hp α β hβ hαβ⟩

lemma strongLinOn_true_iff : I.StrongLinOn (fun _ => True) ↔ I.StronglyLinearizable :=
  ⟨fun ⟨f, hf, hp⟩ => ⟨f, fun α hα => hf α hα trivial, fun α β hβ => hp α β hβ trivial⟩,
    fun h => h.strongLinOn _⟩

lemma nStrongLinOn_true_iff {S : NSpec A.Op A.Resp} :
    I.NStrongLinOn S (fun _ => True) ↔ I.NStronglyLinearizable S :=
  ⟨fun ⟨f, hf, hp⟩ => ⟨f, fun α hα => hf α hα trivial, fun α β hβ => hp α β hβ trivial⟩,
    fun h => h.nStrongLinOn _⟩

lemma StrongLinOn.mono {E E' : List (Label P A) → Prop} (h : I.StrongLinOn E)
    (hE : ∀ α, E' α → E α) : I.StrongLinOn E' := by
  obtain ⟨f, hf, hp⟩ := h
  exact ⟨f, fun α hα h' => hf α hα (hE α h'), fun α β hβ h' hαβ => hp α β hβ (hE β h') hαβ⟩

lemma NStrongLinOn.mono {S : NSpec A.Op A.Resp} {E E' : List (Label P A) → Prop}
    (h : I.NStrongLinOn S E) (hE : ∀ α, E' α → E α) : I.NStrongLinOn S E' := by
  obtain ⟨f, hf, hp⟩ := h
  exact ⟨f, fun α hα h' => hf α hα (hE α h'), fun α β hβ h' hαβ => hp α β hβ (hE β h') hαβ⟩

end Impl

end Cslib.SharedMemory
