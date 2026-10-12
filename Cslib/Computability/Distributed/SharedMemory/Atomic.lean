/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.LinPoints
public import Cslib.Computability.Distributed.SharedMemory.Progress

/-!
# The trivial atomic implementation

Every object `A` has a wait-free, linearizable, *perfect* history-independent implementation
from a single base object of type `A`: each operation applies itself to the base object in one
step and returns the response. (This is the "large base objects" regime; it also shows that the
notions of `Model.lean` are satisfiable, i.e. impossibility results about them are not vacuous.)

-/

@[expose] public section

namespace Cslib.SharedMemory

open List

variable {A : ObjSpec} {P : Type} [DecidableEq P]

/-- Local states of the atomic implementation. -/
inductive AtomicLoc (A : ObjSpec) where
  | idle
  | apply (o : A.Op)
  | done (r : A.Resp)

/-- The atomic implementation of `A` from one base object of type `A` (`r₀` is a dummy response,
never returned). -/
def atomicImpl (A : ObjSpec) (r₀ : A.Resp) (P : Type) :
    Impl A (fun _ : Unit => A) P (AtomicLoc A) where
  memInit _ := A.init
  locInit _ := .idle
  invoke _ _ o := .apply o
  act _ l := match l with
    | .idle => .ret r₀ .idle
    | .apply o => .access () o (fun r => .done r)
    | .done r => .ret r .idle

namespace Atomic

variable {r₀ : A.Resp}

/-- The invariant: `L` is a linearization, the base object holds `linState L`, and the local
state of each process describes the status of its current operation. -/
structure Inv (α : List (Label P A)) (C : Config A (fun _ : Unit => A) P (AtomicLoc A))
    (L : List (OpId P × A.Op)) : Prop where
  lin : IsLinearization α L
  mem : C.mem () = linState L
  idle : ∀ p, C.loc p = .idle ↔ C.pend p = none
  apply : ∀ p o, C.loc p = .apply o → C.pend p = some o ∧
    (p, (respsOf α p).length) ∉ L.map Prod.fst ∧ opOf α (p, (respsOf α p).length) = some o
  done : ∀ p r, C.loc p = .done r → C.pend p ≠ none ∧ ∃ L₁ L₂ o,
    L = L₁ ++ ((p, (respsOf α p).length), o) :: L₂ ∧
    (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).2 = r

theorem inv_of_run {α : List (Label P A)} {C : Config A (fun _ : Unit => A) P (AtomicLoc A)}
    (h : (atomicImpl A r₀ P).run α = some C) : ∃ L, Inv α C L := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run, Impl.runFrom, Impl.initCfg, Option.some.injEq] at h; subst h
    refine ⟨[], ⟨?_, rfl, ?_, ?_, ?_⟩⟩
    · exact ⟨by simp, by simp, fun a ha => by simp [Completed] at ha,
        fun a b hab hb => by simp at hb, trivial⟩
    · intro p; simp [atomicImpl]
    · intro p o h; simp [atomicImpl] at h
    · intro p r h; simp [atomicImpl] at h
  | append_singleton α ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : (atomicImpl A r₀ P).runFrom (atomicImpl A r₀ P).initCfg α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      obtain ⟨L, hI⟩ := ih hα
      have hcnt := (atomicImpl A r₀ P).run_counts hα
      cases ℓ with
      | inv p o =>
        obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
        have hlen : (opsOf α p).length = (respsOf α p).length := by
          rcases hcnt p with ⟨-, h1⟩ | ⟨h1, -⟩
          · exact h1
          · exact absurd h0 h1
        refine ⟨L, hI.lin.append_inv p o, by rw [hmem]; exact hI.mem, ?_, ?_, ?_⟩
        · intro q
          by_cases hq : q = p
          · subst hq; simp [hpend, hloc, atomicImpl]
          · rw [hpend, hloc, Function.update_of_ne hq, Function.update_of_ne hq]; exact hI.idle q
        · intro q o' hq'
          by_cases hq : q = p
          · subst hq
            rw [hloc, Function.update_self] at hq'
            simp only [atomicImpl, AtomicLoc.apply.injEq] at hq'
            subst hq'
            refine ⟨by rw [hpend, Function.update_self], ?_, ?_⟩
            · intro hm
              have := hI.lin.mem_invoked (by simpa using hm)
              simp [Invoked] at this; omega
            · simp [opOf, respsOf_append, opsOf_append, ← hlen]
          · rw [hloc, Function.update_of_ne hq] at hq'
            obtain ⟨h1, h2, h3⟩ := hI.apply q o' hq'
            have hinv : Invoked α (q, (respsOf α q).length) := by
              simp only [opOf] at h3; exact (List.getElem?_eq_some_iff.1 h3).1
            refine ⟨by rw [hpend, Function.update_of_ne hq]; exact h1, by simpa using h2, ?_⟩
            simp only [respsOf_append, respsOf_cons, Label.retOf_inv, Option.toList_none,
              respsOf_nil, append_nil]
            rw [opOf_append_of_invoked hinv]; exact h3
        · intro q r' hq'
          by_cases hq : q = p
          · subst hq; rw [hloc, Function.update_self] at hq'; cases hq'
          · rw [hloc, Function.update_of_ne hq] at hq'
            obtain ⟨h1, h2⟩ := hI.done q r' hq'
            refine ⟨by rw [hpend, Function.update_of_ne hq]; exact h1, ?_⟩
            simpa using h2
      | tau p =>
        obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
        cases hl : C₀.loc p with
        | idle => simp [atomicImpl, hl] at hact
        | done r => simp [atomicImpl, hl] at hact
        | apply o' =>
          simp only [atomicImpl, hl, Action.access.injEq] at hact
          obtain ⟨-, h1, h2⟩ := hact
          have ho : o' = o := eq_of_heq h1
          subst ho
          have hk : k = fun r => AtomicLoc.done r := (eq_of_heq h2).symm
          subst hk
          obtain ⟨hp1, hp2, hp3⟩ := hI.apply p o' hl
          set x : OpId P := (p, (respsOf α p).length)
          have hnc : ¬ Completed α x := by simp [Completed, x]
          refine ⟨L ++ [(x, o')], (hI.lin.push hp3 hp2 hnc).append_tau p, ?_, ?_, ?_, ?_⟩
          · rw [hmem, Function.update_self, hI.mem]
            simp [linState, ObjSpec.runOps_append]
          · intro q
            by_cases hq : q = p
            · subst hq; simp [hpend, hloc, h0]
            · rw [hpend, hloc, Function.update_of_ne hq]; exact hI.idle q
          · intro q o'' hq'
            by_cases hq : q = p
            · subst hq; rw [hloc, Function.update_self] at hq'; cases hq'
            · rw [hloc, Function.update_of_ne hq] at hq'
              obtain ⟨h1, h2, h3⟩ := hI.apply q o'' hq'
              have hinv : Invoked α (q, (respsOf α q).length) := by
                simp only [opOf] at h3; exact (List.getElem?_eq_some_iff.1 h3).1
              refine ⟨by rw [hpend]; exact h1, ?_, ?_⟩
              · simp only [respsOf_append, respsOf_cons, Label.retOf_tau, Option.toList_none,
                  respsOf_nil, append_nil, map_append, map_cons, map_nil, mem_append,
                  mem_singleton, not_or]
                exact ⟨h2, fun h => hq (congrArg Prod.fst h)⟩
              · simp only [respsOf_append, respsOf_cons, Label.retOf_tau, Option.toList_none,
                  respsOf_nil, append_nil]
                rw [opOf_append_of_invoked hinv]; exact h3
          · intro q r' hq'
            by_cases hq : q = p
            · subst hq
              rw [hloc, Function.update_self] at hq'
              simp only [AtomicLoc.done.injEq] at hq'
              refine ⟨by rw [hpend]; exact h0, L, [], o', by simp [x], ?_⟩
              rw [← hq']; cases i; rw [hI.mem]; rfl
            · rw [hloc, Function.update_of_ne hq] at hq'
              obtain ⟨h1, L₁, L₂, o₁, hs, hr⟩ := hI.done q r' hq'
              refine ⟨by rw [hpend]; exact h1, L₁, L₂ ++ [(x, o')], o₁, ?_, hr⟩
              simp [hs]
      | ret p r =>
        obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
        cases hl : C₀.loc p with
        | idle => exact absurd ((hI.idle p).1 hl) h0
        | apply o' => simp [atomicImpl, hl] at hact
        | done r' =>
          simp only [atomicImpl, hl, Action.ret.injEq] at hact
          obtain ⟨hrr, rfl⟩ := hact
          rw [hrr] at hl
          obtain ⟨-, L₁, L₂, o, hs, hr⟩ := hI.done p r hl
          refine ⟨L, hI.lin.append_ret L₁ L₂ o hs hr, by rw [hmem]; exact hI.mem, ?_, ?_, ?_⟩
          · intro q
            by_cases hq : q = p
            · subst hq; simp [hpend, hloc]
            · rw [hpend, hloc, Function.update_of_ne hq, Function.update_of_ne hq]
              exact hI.idle q
          · intro q o'' hq'
            by_cases hq : q = p
            · subst hq; rw [hloc, Function.update_self] at hq'; cases hq'
            · rw [hloc, Function.update_of_ne hq] at hq'
              obtain ⟨h1, h2, h3⟩ := hI.apply q o'' hq'
              have hr' : respsOf (α ++ [Label.ret p r]) q = respsOf α q := by
                simp [respsOf_append, Ne.symm hq]
              refine ⟨by rw [hpend, Function.update_of_ne hq]; exact h1, by rw [hr']; exact h2, ?_⟩
              rw [hr']; simp only [opOf, opsOf_append, opsOf_cons, Label.invOf_ret,
                Option.toList_none, opsOf_nil, append_nil]; exact h3
          · intro q r'' hq'
            by_cases hq : q = p
            · subst hq; rw [hloc, Function.update_self] at hq'; cases hq'
            · rw [hloc, Function.update_of_ne hq] at hq'
              obtain ⟨h1, h2⟩ := hI.done q r'' hq'
              have hr' : respsOf (α ++ [Label.ret p r]) q = respsOf α q := by
                simp [respsOf_append, Ne.symm hq]
              refine ⟨by rw [hpend, Function.update_of_ne hq]; exact h1, ?_⟩
              rw [hr']; exact h2

theorem exists_linFun : ∃ h : List (Label P A) → List (OpId P × A.Op),
    ∀ α C, (atomicImpl A r₀ P).run α = some C → Inv α C (h α) := by
  have : ∀ α : List (Label P A), ∃ L, ∀ C, (atomicImpl A r₀ P).run α = some C → Inv α C L := by
    intro α
    cases hα : (atomicImpl A r₀ P).run α with
    | none => exact ⟨[], fun C h => by cases h⟩
    | some C =>
      obtain ⟨L, hL⟩ := inv_of_run hα
      exact ⟨L, fun C' h => by cases h; exact hL⟩
  choose h hh using this
  exact ⟨h, hh⟩

/-- The atomic implementation is linearizable and perfectly history independent. -/
theorem perfectHI : (atomicImpl A r₀ P).PerfectHI := by
  obtain ⟨h, hh⟩ := exists_linFun (A := A) (P := P) (r₀ := r₀)
  refine ⟨h, fun α ⟨C, hC⟩ => (hh α C hC).lin, fun α α' C C' h1 h2 _ _ hl => ?_⟩
  funext i
  cases i
  rw [(hh α C h1).mem, (hh α' C' h2).mem, hl]

/-- The atomic implementation is wait-free. -/
theorem waitFree : (atomicImpl A r₀ P).WaitFree := by
  intro e p n hpend
  by_cases hex : ∃ m ≥ n, e.lbl m = .tau p
  · obtain ⟨m, hm, hlbl⟩ := hex
    have hdone : ∀ j, ∃ r, (e.cfg (m + 1 + j)).loc p = .done r := by
      intro j
      induction j with
      | zero =>
        have hs := e.step_eq m
        rw [hlbl] at hs
        obtain ⟨-, -, i, o, k, hact, -, hloc⟩ := Impl.step_tau hs
        cases hl : (e.cfg m).loc p with
        | idle => simp [atomicImpl, hl] at hact
        | done r => simp [atomicImpl, hl] at hact
        | apply o' =>
          simp only [atomicImpl, hl, Action.access.injEq] at hact
          obtain ⟨-, -, h2⟩ := hact
          have hk : k = fun r => AtomicLoc.done r := (eq_of_heq h2).symm
          subst hk
          exact ⟨_, by rw [Nat.add_zero, hloc, Function.update_self]⟩
      | succ j ih =>
        obtain ⟨r, hr⟩ := ih
        have hs := e.step_eq (m + 1 + j)
        rw [show m + 1 + (j + 1) = m + 1 + j + 1 by omega]
        by_cases hq : (e.lbl (m + 1 + j)).proc = p
        · exfalso
          cases hl : e.lbl (m + 1 + j) with
          | inv q o =>
            rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
            exact hpend (m + 1 + j) (by omega) (Impl.step_inv hs).1
          | tau q =>
            rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
            obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
            simp [atomicImpl, hr] at hact
          | ret q r' =>
            rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
            exact hpend (m + 1 + j + 1) (by omega) (by simp [(Impl.step_ret hs).2.1])
        · exact ⟨r, by rw [(Impl.step_other hs hq).1, hr]⟩
    refine ⟨m + 1, fun m' hm' heq => ?_⟩
    obtain ⟨r, hr⟩ := hdone (m' - (m + 1))
    rw [show m + 1 + (m' - (m + 1)) = m' by omega] at hr
    have hs := e.step_eq m'
    rw [heq] at hs
    obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
    simp [atomicImpl, hr] at hact
  · push Not at hex
    exact ⟨n, hex⟩

end Atomic

end Cslib.SharedMemory
