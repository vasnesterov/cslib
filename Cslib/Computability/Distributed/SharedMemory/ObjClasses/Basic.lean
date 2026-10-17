/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Spec
public import Cslib.Computability.Distributed.SharedMemory.Objects.Queue
public import Cslib.Computability.Distributed.SharedMemory.Objects.Window

/-!
# Interfering, window-like and stack-like objects

Semantic *classes* of base objects, used to state impossibility results for all objects of a
class at once:

* `ObjSpec.CommuteAt`, `ObjSpec.OverwritesAt`, `ObjSpec.Interfering` — Herlihy's *interfering*
  primitives: at every state, any two operations commute or one overwrites the other
  (read, write, test&set, swap, fetch&add, …);
* `ObjSpec.WindowLike S w` — every operation is read-only or has a state-independent response
  ("write"), and any `w` consecutive non-read-only operations determine the state;
  `windowObj V w'` is `WindowLike` for every `w ≥ w'`;
* `StackRep S V`, `ObjSpec.StackLike` — the object is (isomorphic to) a stack.

Further classes (read/write-like, test&set-like, readable, …) are in
`Cslib.Computability.Distributed.SharedMemory.ObjClasses`.
-/

@[expose] public section

namespace Cslib.SharedMemory

/-! ## Interfering objects -/

namespace ObjSpec

variable (S : ObjSpec)

/-- `o₁` and `o₂` commute at `s` (Herlihy): both orders lead to the same state. -/
def CommuteAt (s : S.State) (o₁ o₂ : S.Op) : Prop :=
  (S.δ (S.δ s o₁).1 o₂).1 = (S.δ (S.δ s o₂).1 o₁).1

/-- `o₁` overwrites `o₂` at `s` (Herlihy): applying `o₂` and then `o₁` leads to the same state as
applying `o₁` alone. -/
def OverwritesAt (s : S.State) (o₁ o₂ : S.Op) : Prop :=
  (S.δ (S.δ s o₂).1 o₁).1 = (S.δ s o₁).1

/-- Herlihy's *interfering* objects: at every state, any two operations commute or one of them
overwrites the other. -/
def Interfering : Prop :=
  ∀ s o₁ o₂, S.CommuteAt s o₁ o₂ ∨ S.OverwritesAt s o₁ o₂ ∨ S.OverwritesAt s o₂ o₁

/-- *Window-like* objects with window `w`: every operation is read-only or a "write" whose
response does not depend on the state, and any sequence of at least `w` non-read-only operations
leads to a state that does not depend on the starting state. -/
def WindowLike (w : ℕ) : Prop :=
  (∀ o, S.ReadOnly o ∨ ∀ s s', (S.δ s o).2 = (S.δ s' o).2) ∧
  ∀ os : List S.Op, os ≠ [] → w ≤ os.length → (∀ o ∈ os, ¬ S.ReadOnly o) →
    ∀ s s', S.runOps s os = S.runOps s' os

/-- Window-likeness is monotone in the window size. -/
lemma WindowLike.mono {S : ObjSpec} {w w' : ℕ} (h : S.WindowLike w) (hw : w ≤ w') :
    S.WindowLike w' :=
  ⟨h.1, fun os hne hos hro s s' => h.2 os hne (hw.trans hos) hro s s'⟩

end ObjSpec

/-- A representation of the object `S` as a stack over `V`: states are (injectively) lists,
every operation is a `push v` or a `pop`, with the stack's effect and responses. -/
structure StackRep (S : ObjSpec) (V : Type) where
  /-- The stack contents (top first). -/
  toList : S.State → List V
  /-- Different states have different contents. -/
  inj : Function.Injective toList
  /-- `some v`: the operation pushes `v`; `none`: it pops. -/
  push : S.Op → Option V
  /-- A push adds its value on top. -/
  push_state : ∀ s o v, push o = some v → toList (S.δ s o).1 = v :: toList s
  /-- The response of a push does not depend on the state. -/
  push_resp : ∀ s s' o v, push o = some v → (S.δ s o).2 = (S.δ s' o).2
  /-- A pop removes the top element. -/
  pop_state : ∀ s o, push o = none → toList (S.δ s o).1 = (toList s).tail
  /-- The response of a pop only depends on the top element. -/
  pop_resp : ∀ s s' o, push o = none → (toList s).head? = (toList s').head? →
    (S.δ s o).2 = (S.δ s' o).2

/-- The object is (isomorphic to) a stack. -/
def ObjSpec.StackLike (S : ObjSpec) : Prop := ∃ V : Type, Nonempty (StackRep S V)

/-! ## The standard objects belong to the classes -/

/-- The stack is represented as a stack by itself. -/
def stackObj.rep (V : Type) : StackRep (stackObj V) V where
  toList s := s
  inj := fun _ _ h => h
  push
    | .push v => some v
    | .pop => none
  push_state s o v h := by cases o <;> simp_all
  push_resp s s' o v h := by cases o <;> simp_all
  pop_state s o h := by cases o <;> simp_all
  pop_resp s s' o h h' := by cases o <;> simp_all

/-- The stack is stack-like. -/
lemma stackObj_stackLike (V : Type) : (stackObj V).StackLike := ⟨V, ⟨stackObj.rep V⟩⟩

/-- A `w'`-window register is window-like with window `w` for every `w ≥ w'`. -/
lemma windowObj_windowLike (V : Type) {w' w : ℕ} (hw : w' ≤ w) :
    (windowObj V w').WindowLike w := by
  refine ⟨fun o => ?_, fun os hne hos hro s s' => ?_⟩
  · cases o with
    | write v => exact Or.inr fun s s' => rfl
    | read => exact Or.inl fun s => rfl
  · have hw : ∀ o ∈ os, ∃ v, o = WinOp.write v := by
      intro o ho
      cases o with
      | write v => exact ⟨v, rfl⟩
      | read => exact absurd (fun s => rfl) (hro _ ho)
    obtain ⟨vs, rfl⟩ : ∃ vs : List V, os = vs.map WinOp.write := by
      clear hos hro hne
      induction os with
      | nil => exact ⟨[], rfl⟩
      | cons o os ih =>
        obtain ⟨v, rfl⟩ := hw o (by simp)
        obtain ⟨vs, rfl⟩ := ih (fun o ho => hw o (by simp [ho]))
        exact ⟨v :: vs, rfl⟩
    obtain ⟨v, vs, rfl⟩ : ∃ v vs', vs = v :: vs' := by
      cases vs with
      | nil => simp at hne
      | cons v vs' => exact ⟨v, vs', rfl⟩
    simp only [List.length_map] at hos
    rw [windowObj_runOps_writes, windowObj_runOps_writes,
      List.drop_length_sub_append_eq _ (by omega), List.drop_length_sub_append_eq _ (by omega)]

/-- Read/write registers are interfering (a read commutes with everything, a write overwrites
everything). -/
lemma register_interfering (V : Type) (v₀ : V) : (register V v₀).Interfering := by
  intro s o₁ o₂
  cases o₁ <;> cases o₂ <;> simp [ObjSpec.CommuteAt, ObjSpec.OverwritesAt]

/-- Window registers with window `1` are standard registers: interfering. -/
lemma windowObj_one_interfering (V : Type) : (windowObj V 1).Interfering := by
  intro s o₁ o₂
  cases o₁ <;> cases o₂ <;> simp [ObjSpec.CommuteAt, ObjSpec.OverwritesAt]

end Cslib.SharedMemory
