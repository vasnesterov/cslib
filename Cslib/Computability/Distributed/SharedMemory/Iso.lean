/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Task

/-!
# Isomorphisms of sequential specifications

An isomorphism `ObjSpec.Iso S S'` consists of equivalences of the states, operations and
responses of `S` and `S'` that map the initial state to the initial state and commute with the
transition functions. Isomorphic objects are "the same object up to renaming".

Replacing the base objects of an implementation by isomorphic ones (`Impl.mapBase`) does not
change anything observable: executions correspond label by label (`Impl.runFrom_mapBase`), so
validity, linearizability, wait-freedom, lock-freedom, obstruction-freedom and solving a task
transfer (`Impl.valid_mapBase_iff`, `Impl.linearizable_mapBase_iff`, …).

## Main definitions

* `ObjSpec.Iso S S'` with `ObjSpec.Iso.refl`, `ObjSpec.Iso.symm`, `ObjSpec.Iso.trans`;
* `Impl.mapBase e I` — the implementation `I` with base objects renamed along `e`;
* `Config.mapMem e C` — the corresponding configuration.
-/

@[expose] public section

namespace Cslib.SharedMemory

/-- An isomorphism of sequential specifications: equivalences of states, operations and
responses preserving the initial state and commuting with the transition functions. -/
structure ObjSpec.Iso (S S' : ObjSpec) where
  /-- The equivalence of states. -/
  state : S.State ≃ S'.State
  /-- The equivalence of operations. -/
  op : S.Op ≃ S'.Op
  /-- The equivalence of responses. -/
  resp : S.Resp ≃ S'.Resp
  /-- The initial state is preserved. -/
  map_init : state S.init = S'.init
  /-- The transition functions commute with the equivalences. -/
  map_δ : ∀ s o, S'.δ (state s) (op o) = (state (S.δ s o).1, resp (S.δ s o).2)

namespace ObjSpec.Iso

variable {S S' S'' : ObjSpec}

/-- The identity isomorphism. -/
@[simps!]
def refl (S : ObjSpec) : S.Iso S :=
  ⟨.refl _, .refl _, .refl _, rfl, fun _ _ => rfl⟩

/-- The inverse isomorphism. -/
@[simps!]
def symm (e : S.Iso S') : S'.Iso S where
  state := e.state.symm
  op := e.op.symm
  resp := e.resp.symm
  map_init := by rw [← e.map_init, Equiv.symm_apply_apply]
  map_δ s o := by
    have h := e.map_δ (e.state.symm s) (e.op.symm o)
    simp only [Equiv.apply_symm_apply] at h
    simp [h]

/-- Composition of isomorphisms. -/
@[simps!]
def trans (e : S.Iso S') (e' : S'.Iso S'') : S.Iso S'' where
  state := e.state.trans e'.state
  op := e.op.trans e'.op
  resp := e.resp.trans e'.resp
  map_init := by simp [e.map_init, e'.map_init]
  map_δ s o := by simp [e.map_δ, e'.map_δ]

/-- Isomorphisms commute with running sequences of operations. -/
lemma map_runOps (e : S.Iso S') (s : S.State) (os : List S.Op) :
    S'.runOps (e.state s) (os.map e.op) = e.state (S.runOps s os) := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => simp [e.map_δ, ih]

end ObjSpec.Iso

/-! ## Renaming the base objects of an implementation -/

variable {A : ObjSpec} {ι : Type} {B B' : ι → ObjSpec} {P L : Type}
  (e : ∀ i, (B i).Iso (B' i))

/-- An action with the base objects renamed along `e`. -/
def Action.mapBase : Action A B L → Action A B' L
  | .access i o k => .access i ((e i).op o) (fun r => k ((e i).resp.symm r))
  | .ret r l => .ret r l

/-- A configuration with the base objects renamed along `e` (local states and pending
operations are unchanged). -/
def Config.mapMem (C : Config A B P L) : Config A B' P L :=
  ⟨C.loc, C.pend, fun i => (e i).state (C.mem i)⟩

/-- Renaming keeps the local states. -/
@[simp] lemma Config.mapMem_loc (C : Config A B P L) : (C.mapMem e).loc = C.loc := rfl

/-- Renaming keeps the pending operations. -/
@[simp] lemma Config.mapMem_pend (C : Config A B P L) : (C.mapMem e).pend = C.pend := rfl

/-- Renaming maps the state of every base object. -/
@[simp] lemma Config.mapMem_mem (C : Config A B P L) (i : ι) :
    (C.mapMem e).mem i = (e i).state (C.mem i) := rfl

/-- Renaming back along the inverse isomorphisms is the identity. -/
@[simp] lemma Config.mapMem_symm_mapMem (C : Config A B P L) :
    (C.mapMem e).mapMem (fun i => (e i).symm) = C := by
  cases C; simp [Config.mapMem]

/-- Renaming along the inverse isomorphisms and back is the identity. -/
@[simp] lemma Config.mapMem_mapMem_symm (C : Config A B' P L) :
    (C.mapMem fun i => (e i).symm).mapMem e = C := by
  cases C; simp [Config.mapMem]

/-- Renaming the base objects is injective on configurations. -/
lemma Config.mapMem_injective :
    Function.Injective (Config.mapMem (A := A) (P := P) (L := L) e) :=
  Function.LeftInverse.injective (Config.mapMem_symm_mapMem e)

namespace Impl

/-- The implementation `I` with its base objects renamed along `e`: every primitive is
translated by `e`, and its response translated back. -/
def mapBase (I : Impl A B P L) : Impl A B' P L where
  memInit i := (e i).state (I.memInit i)
  locInit := I.locInit
  invoke := I.invoke
  act p l := (I.act p l).mapBase e
  allowed := I.allowed

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

omit [DecidableEq P] [DecidableEq ι] in
/-- The initial configuration of the renamed implementation. -/
@[simp] lemma initCfg_mapBase : (I.mapBase e).initCfg = I.initCfg.mapMem e := rfl

/-- Steps of the renamed implementation correspond to steps of the original one. -/
lemma step_mapBase (C : Config A B P L) (ℓ : Label P A) :
    (I.mapBase e).step (C.mapMem e) ℓ = (I.step C ℓ).map (Config.mapMem e) := by
  cases ℓ with
  | inv p o =>
    simp only [step, mapBase, Config.mapMem_pend, Config.mapMem_loc]
    by_cases h : C.pend p = none ∧ I.allowed p o
    · simp only [h, and_self, ↓reduceIte, Option.map_some]; rfl
    · simp only [h, ↓reduceIte, Option.map_none]
  | tau p =>
    simp only [step, Config.mapMem_pend, Config.mapMem_loc]
    by_cases hp : C.pend p = none
    · simp only [hp, ↓reduceIte, Option.map_none]
    · simp only [hp, ↓reduceIte, mapBase]
      cases I.act p (C.loc p) with
      | access i o k =>
        simp only [Action.mapBase, (e i).map_δ, Equiv.symm_apply_apply,
          Option.map_some, Option.some.injEq, Config.mapMem, Config.mk.injEq, true_and]
        funext j
        exact (Function.apply_update (fun j => (e j).state) C.mem i _ j).symm
      | ret r l => rfl
  | ret p r =>
    simp only [step, Config.mapMem_pend, Config.mapMem_loc]
    by_cases hp : C.pend p = none
    · simp only [hp, ↓reduceIte, Option.map_none]
    · simp only [hp, ↓reduceIte, mapBase]
      cases I.act p (C.loc p) with
      | access i o k => rfl
      | ret r' l =>
        simp only [Action.mapBase]
        by_cases hr : r = r'
        · simp only [hr, ↓reduceIte, Option.map_some]; rfl
        · simp only [hr, ↓reduceIte, Option.map_none]

/-- Executions of the renamed implementation correspond to executions of the original one. -/
lemma runFrom_mapBase (C : Config A B P L) (α : List (Label P A)) :
    (I.mapBase e).runFrom (C.mapMem e) α = (I.runFrom C α).map (Config.mapMem e) := by
  induction α generalizing C with
  | nil => rfl
  | cons ℓ α ih =>
    simp only [runFrom_cons, step_mapBase]
    cases I.step C ℓ with
    | none => rfl
    | some C' => simp [ih]

/-- Executions from the initial configuration correspond. -/
lemma run_mapBase (α : List (Label P A)) :
    (I.mapBase e).run α = (I.run α).map (Config.mapMem e) :=
  I.runFrom_mapBase e I.initCfg α

/-- Renaming the base objects does not change the set of executions. -/
lemma valid_mapBase_iff {α : List (Label P A)} : (I.mapBase e).Valid α ↔ I.Valid α := by
  simp [Valid, run_mapBase]

/-- Renaming the base objects preserves linearization functions. -/
lemma isLinFun_mapBase_iff {h : List (Label P A) → List (OpId P × A.Op)} :
    (I.mapBase e).IsLinFun h ↔ I.IsLinFun h := by
  simp only [IsLinFun, valid_mapBase_iff]

/-- Renaming the base objects preserves linearizability. -/
lemma linearizable_mapBase_iff : (I.mapBase e).Linearizable ↔ I.Linearizable := by
  simp only [Linearizable, isLinFun_mapBase_iff]

/-- Renaming the base objects preserves solving a task. -/
lemma solves_mapBase_iff (T : Task P) [Inhabited T.Out] (I : Impl (taskObj T.In T.Out) B P L) :
    (I.mapBase e).Solves T ↔ I.Solves T := by
  simp only [Solves, valid_mapBase_iff]

/-- Steps of the renamed implementation from an arbitrary configuration. -/
lemma step_mapBase' (C : Config A B' P L) (ℓ : Label P A) :
    (I.mapBase e).step C ℓ =
      (I.step (C.mapMem fun i => (e i).symm) ℓ).map (Config.mapMem e) := by
  conv_lhs => rw [← Config.mapMem_mapMem_symm e C]
  exact I.step_mapBase e _ ℓ

/-- An infinite execution of `I` as one of the renamed implementation. -/
def InfExec.mapBase (x : I.InfExec) : (I.mapBase e).InfExec where
  cfg n := (x.cfg n).mapMem e
  lbl := x.lbl
  cfg_zero := by rw [x.cfg_zero]; rfl
  step_eq n := by rw [step_mapBase, x.step_eq]; rfl

/-- An infinite execution of the renamed implementation as one of `I`. -/
def InfExec.unmapBase (x : (I.mapBase e).InfExec) : I.InfExec where
  cfg n := (x.cfg n).mapMem fun i => (e i).symm
  lbl := x.lbl
  cfg_zero := by rw [x.cfg_zero]; simp
  step_eq n := by
    have h := x.step_eq n
    rw [step_mapBase'] at h
    obtain ⟨C, hC, hC'⟩ := Option.map_eq_some_iff.1 h
    rw [hC, ← hC', Config.mapMem_symm_mapMem]

/-- Renaming the base objects preserves wait-freedom. -/
lemma waitFree_mapBase_iff : (I.mapBase e).WaitFree ↔ I.WaitFree :=
  ⟨fun h x p n hp => h (InfExec.mapBase e I x) p n hp,
    fun h x p n hp => h (InfExec.unmapBase e I x) p n hp⟩

/-- Renaming the base objects preserves lock-freedom. -/
lemma lockFree_mapBase_iff : (I.mapBase e).LockFree ↔ I.LockFree :=
  ⟨fun h x hx => h (InfExec.mapBase e I x) hx, fun h x hx => h (InfExec.unmapBase e I x) hx⟩

omit [DecidableEq P] [DecidableEq ι] in
/-- The next label of a process is unchanged by renaming the base objects. -/
lemma nextLabel_mapBase (C : Config A B P L) (p : P) :
    (I.mapBase e).nextLabel (C.mapMem e) p = I.nextLabel C p := by
  simp only [nextLabel, mapBase, Config.mapMem_loc]
  cases I.act p (C.loc p) <;> rfl

/-- Solo steps correspond. -/
lemma soloStep_mapBase (p : P) (C : Config A B P L) :
    (I.mapBase e).soloStep p (C.mapMem e) = (I.soloStep p C).mapMem e := by
  simp only [soloStep, Config.mapMem_pend, nextLabel_mapBase, step_mapBase]
  split_ifs
  · rfl
  · cases I.step C (I.nextLabel C p) <;> rfl

/-- Solo runs correspond. -/
lemma iterate_soloStep_mapBase (p : P) (C : Config A B P L) (k : ℕ) :
    ((I.mapBase e).soloStep p)^[k] (C.mapMem e) = ((I.soloStep p)^[k] C).mapMem e := by
  induction k generalizing C with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply, soloStep_mapBase, ih]

/-- Reachable configurations correspond. -/
lemma reachable_mapBase_iff (C : Config A B P L) :
    (I.mapBase e).Reachable (C.mapMem e) ↔ I.Reachable C := by
  simp only [Reachable, run_mapBase, Option.map_eq_some_iff,
    (Config.mapMem_injective e).eq_iff, exists_eq_right]

/-- Renaming the base objects preserves obstruction-freedom. -/
lemma obstructionFree_mapBase_iff : (I.mapBase e).ObstructionFree ↔ I.ObstructionFree := by
  constructor
  · intro h C p hC hp
    obtain ⟨k, hk⟩ := h (C.mapMem e) p ((I.reachable_mapBase_iff e C).2 hC) hp
    exact ⟨k, by rwa [iterate_soloStep_mapBase] at hk⟩
  · intro h C p hC hp
    obtain ⟨D, rfl⟩ : ∃ D : Config A B P L, D.mapMem e = C :=
      ⟨_, Config.mapMem_mapMem_symm e C⟩
    obtain ⟨k, hk⟩ := h D p ((I.reachable_mapBase_iff e D).1 hC) hp
    exact ⟨k, by rw [iterate_soloStep_mapBase]; exact hk⟩

end Impl

end Cslib.SharedMemory
