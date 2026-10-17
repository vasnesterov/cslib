/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.StrongLin
public import Cslib.Computability.Distributed.SharedMemory.Potential

/-!
# Single-access implementations are strongly linearizable

A *single-access* implementation executes every high-level operation with exactly one access to
one base object: in local datum `d`, an invocation of `o` by `p` applies primitive
`prim p d o` to object `obj p d o`, updates its local datum to `upd p d o r` and returns
`out p d o r`, where `r` is the primitive's response.

If there is an *abstraction relation* `Abs mem data s` between the memory, the local data of all
processes and an abstract state `s` that is preserved by every such access (with the access
returning the specification's response), then the implementation is wait-free and strongly
linearizable: every operation is linearized at its unique access, which is a fixed point of the
execution (`OneAccess.stronglyLinearizable`, `OneAccess.waitFree`).

Examples: the trivial atomic implementation; the max register and the atomic snapshot from
`fetch&add` of Attiya, Castañeda and Enea (PODC 2024, Theorems 1 and 2).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P D : Type}

/-- Local states of a single-access implementation (with a persistent local datum). -/
inductive OALoc (D : Type) (A : ObjSpec) where
  /-- No pending operation. -/
  | idle (d : D)
  /-- Pending operation `o`, before its access. -/
  | pend (d : D) (o : A.Op)
  /-- After the access, about to return `r`. -/
  | done (d : D) (r : A.Resp)

/-- The local datum. -/
def OALoc.data : OALoc D A → D
  | .idle d => d
  | .pend d _ => d
  | .done d _ => d

/-- A single-access implementation scheme. -/
structure OneAccess (A : ObjSpec) (B : ι → ObjSpec) (P D : Type) where
  /-- Initial memory. -/
  memInit : (i : ι) → (B i).State
  /-- Initial local data. -/
  dInit : P → D
  /-- The base object accessed by the operation. -/
  obj : P → D → A.Op → ι
  /-- The primitive applied. -/
  prim : (p : P) → (d : D) → (o : A.Op) → (B (obj p d o)).Op
  /-- The new local datum, given the primitive's response. -/
  upd : (p : P) → (d : D) → (o : A.Op) → (B (obj p d o)).Resp → D
  /-- The response returned, given the primitive's response. -/
  out : (p : P) → (d : D) → (o : A.Op) → (B (obj p d o)).Resp → A.Resp
  /-- Which operations a process may invoke. -/
  allowed : P → A.Op → Prop := fun _ _ => True

namespace OneAccess

variable (S : OneAccess A B P D)

/-- The implementation (`r₀` is a dummy response, never returned). -/
def impl (r₀ : A.Resp) : Impl A B P (OALoc D A) where
  memInit := S.memInit
  locInit p := .idle (S.dInit p)
  invoke _ l o := .pend l.data o
  act p l := match l with
    | .idle d => .ret r₀ (.idle d)
    | .pend d o => .access (S.obj p d o) (S.prim p d o)
        (fun r => .done (S.upd p d o r) (S.out p d o r))
    | .done d r => .ret r (.idle d)
  allowed := S.allowed

variable [DecidableEq P] [DecidableEq ι]

/-- An abstraction relation preserved by every access (`d` is the datum of the accessing
process `p`). -/
structure Sim (Abs : ((i : ι) → (B i).State) → (P → D) → A.State → Prop) : Prop where
  init : Abs S.memInit S.dInit A.init
  step : ∀ m ds s p d o, ds p = d → Abs m ds s → S.allowed p o →
    Abs (Function.update m (S.obj p d o)
          ((B (S.obj p d o)).δ (m (S.obj p d o)) (S.prim p d o)).1)
        (Function.update ds p (S.upd p d o
          ((B (S.obj p d o)).δ (m (S.obj p d o)) (S.prim p d o)).2))
        (A.δ s o).1 ∧
    S.out p d o ((B (S.obj p d o)).δ (m (S.obj p d o)) (S.prim p d o)).2 = (A.δ s o).2

/-- Status of a process, as a function of its local state. -/
def St (α : List (Label P A)) (C : Config A B P (OALoc D A)) (Lin : List (OpId P × A.Op))
    (p : P) : Prop :=
  match C.loc p with
  | .idle _ => C.pend p = none
  | .pend _ o => C.pend p = some o ∧ S.allowed p o ∧ curOp α p ∉ Lin.map Prod.fst ∧
      opOf α (curOp α p) = some o
  | .done _ r => C.pend p ≠ none ∧ A.respIn A.init Lin (curOp α p) = some r

/-- The simulation invariant. -/
structure Inv (Abs : ((i : ι) → (B i).State) → (P → D) → A.State → Prop)
    (α : List (Label P A)) (C : Config A B P (OALoc D A)) (Lin : List (OpId P × A.Op)) :
    Prop where
  lin : IsLinearization α Lin
  abs : Abs C.mem (fun p => (C.loc p).data) (linState Lin)
  st : ∀ p, S.St α C Lin p

lemma linSim {Abs : ((i : ι) → (B i).State) → (P → D) → A.State → Prop} (hS : S.Sim Abs)
    (r₀ : A.Resp) : (S.impl r₀).LinSim (S.Inv Abs) where
  init := ⟨isLinearization_nil, by simpa [impl, Impl.initCfg, OALoc.data, linState] using hS.init,
    fun p => by simp [St, impl, Impl.initCfg]⟩
  lin _ _ _ _ h := h.lin
  step := by
    intro α C Lin ℓ C' hrun hI hstep
    have hcnt := (S.impl r₀).run_counts hrun
    cases ℓ with
    | inv p o =>
      obtain ⟨h0, hal, hpend, hloc, hmem⟩ := Impl.step_inv hstep
      have hlen : (opsOf α p).length = (respsOf α p).length := by
        rcases hcnt p with ⟨-, h1⟩ | ⟨h1, -⟩
        · exact h1
        · exact absurd h0 h1
      have hdata : (fun q => (C'.loc q).data) = (fun q => (C.loc q).data) := by
        funext q
        by_cases hq : q = p
        · subst hq; simp [hloc, impl, OALoc.data]
        · simp [hloc, Function.update_of_ne hq]
      refine ⟨[], ?_⟩
      rw [List.append_nil]
      refine ⟨hI.lin.append_inv p o, by rw [hmem, hdata]; exact hI.abs, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq
        simp only [St, hloc, Function.update_self, impl, hpend]
        refine ⟨trivial, hal, ?_, ?_⟩
        · rw [curOp_append_inv]
          intro hm
          have := hI.lin.invoked_of_mem hm
          simp [Invoked] at this; omega
        · simp [opOf, respsOf_append, opsOf_append, ← hlen]
      · have hpq : (Label.inv p o : Label P A).proc ≠ q := by simpa [Label.proc] using Ne.symm hq
        have h1 := hI.st q
        simp only [St, hloc, hpend, Function.update_of_ne hq, curOp_append_of_proc_ne α hpq] at h1 ⊢
        split at h1
        · exact h1
        · obtain ⟨a, b, c, d⟩ := h1
          refine ⟨a, b, c, ?_⟩
          have hinv : Invoked α (curOp α q) := by
            simp only [opOf] at d; exact (List.getElem?_eq_some_iff.1 d).1
          rw [opOf_append_of_invoked hinv]; exact d
        · exact h1
    | tau p =>
      obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hstep
      have hst := hI.st p
      cases hl : C.loc p with
      | idle d => simp [impl, hl] at hact
      | done d r => simp [impl, hl] at hact
      | pend d o' =>
        simp only [impl, hl, Action.access.injEq] at hact
        obtain ⟨hi, ho, hk⟩ := hact
        subst hi
        have ho' : S.prim p d o' = o := eq_of_heq ho
        subst ho'
        have hk' : k = fun r => OALoc.done (S.upd p d o' r) (S.out p d o' r) := (eq_of_heq hk).symm
        subst hk'
        simp only [St, hl] at hst
        obtain ⟨hp1, hal, hp2, hp3⟩ := hst
        have hnc : ¬ Completed α (curOp α p) := by simp [Completed]
        refine ⟨[(curOp α p, o')], (hI.lin.push hp3 hp2 hnc).append_tau p, ?_, fun q => ?_⟩
        · have hd : (fun q => (C.loc q).data) p = d := by simp [hl, OALoc.data]
          have key := (hS.step C.mem (fun q => (C.loc q).data) (linState Lin) p d o' hd hI.abs
            hal).1
          convert key using 1
          · funext q
            by_cases hq : q = p
            · subst hq; simp [hloc, OALoc.data]
            · simp [hloc, Function.update_of_ne hq]
          · simp [linState, ObjSpec.runOps_append]
        · have hpq : ∀ q, q ≠ p → (Label.tau p : Label P A).proc ≠ q :=
            fun q hq => by simpa [Label.proc] using Ne.symm hq
          by_cases hq : q = p
          · subst hq
            simp only [St, hloc, Function.update_self, hpend]
            refine ⟨h0, ?_⟩
            rw [curOp_append_tau, ObjSpec.respIn_concat_self hp2]
            have hd : (fun q => (C.loc q).data) q = d := by simp [hl, OALoc.data]
            have key := (hS.step C.mem (fun q => (C.loc q).data) (linState Lin) q d o' hd hI.abs
              hal).2
            rw [key]
            rfl
          · have h1 := hI.st q
            simp only [St, hloc, hpend, Function.update_of_ne hq,
              curOp_append_of_proc_ne α (hpq q hq)] at h1 ⊢
            split at h1
            · exact h1
            · obtain ⟨a, b, c, d⟩ := h1
              refine ⟨a, b, ?_, ?_⟩
              · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
                  List.mem_singleton, not_or]
                exact ⟨c, fun h => hq (congrArg Prod.fst h)⟩
              · have hinv : Invoked α (curOp α q) := by
                  simp only [opOf] at d; exact (List.getElem?_eq_some_iff.1 d).1
                rw [opOf_append_of_invoked hinv]; exact d
            · obtain ⟨a, b⟩ := h1
              refine ⟨a, ?_⟩
              rw [ObjSpec.respIn_append_of_eq_some b]
    | ret p r =>
      obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hstep
      have hst := hI.st p
      cases hl : C.loc p with
      | idle d => simp only [St, hl] at hst; exact absurd hst h0
      | pend d o' => simp [impl, hl] at hact
      | done d r' =>
        simp only [impl, hl, Action.ret.injEq] at hact
        obtain ⟨rfl, rfl⟩ := hact
        simp only [St, hl] at hst
        refine ⟨[], ?_⟩
        rw [List.append_nil]
        have hdata : (fun q => (C'.loc q).data) = (fun q => (C.loc q).data) := by
          funext q
          by_cases hq : q = p
          · subst hq; simp [hloc, hl, OALoc.data]
          · simp [hloc, Function.update_of_ne hq]
        refine ⟨hI.lin.append_ret_of_respIn hst.2, by rw [hmem, hdata]; exact hI.abs, fun q => ?_⟩
        by_cases hq : q = p
        · subst hq; simp [St, hloc, hpend]
        · have hpq : (Label.ret p r' : Label P A).proc ≠ q := by
            simpa [Label.proc] using Ne.symm hq
          have h1 := hI.st q
          simp only [St, hloc, hpend, Function.update_of_ne hq, curOp_append_of_proc_ne α hpq]
            at h1 ⊢
          split at h1
          · exact h1
          · obtain ⟨a, b, c, d⟩ := h1
            refine ⟨a, b, c, ?_⟩
            simp only [opOf, opsOf_append, opsOf_cons, Label.invOf_ret, Option.toList_none,
              opsOf_nil, List.append_nil]
            exact d
          · exact h1

/-- **Single-access implementations with an abstraction relation are strongly
linearizable.** -/
theorem stronglyLinearizable {Abs : ((i : ι) → (B i).State) → (P → D) → A.State → Prop}
    (hS : S.Sim Abs) (r₀ : A.Resp) : (S.impl r₀).StronglyLinearizable :=
  (S.impl r₀).stronglyLinearizable_of_linSim _ (S.linSim hS r₀)

/-- Single-access implementations are wait-free (one access per operation). -/
theorem waitFree (r₀ : A.Resp) : (S.impl r₀).WaitFree := by
  refine (S.impl r₀).waitFree_of_potential
    (fun _ l => match l with | .pend _ _ => 1 | _ => 0) ?_
  intro p l i o k hact x
  cases l with
  | idle d => simp [impl] at hact
  | done d r => simp [impl] at hact
  | pend d o' =>
    simp only [impl, Action.access.injEq] at hact
    obtain ⟨rfl, -, hk⟩ := hact
    rw [← eq_of_heq hk]
    simp

end OneAccess

end Cslib.SharedMemory
