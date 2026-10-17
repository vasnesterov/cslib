/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Covering
public import Cslib.Computability.Distributed.SharedMemory.ObjClasses.Basic
public import Cslib.Computability.Distributed.SharedMemory.Objects.Swap
public import Cslib.Computability.Distributed.SharedMemory.Objects.TestAndSet

/-!
# Classes of base objects

Semantic classes of sequential objects, used to state results for all objects of a class at
once. Besides the classes of `Cslib.Computability.Distributed.SharedMemory.ObjClasses.Basic`
(interfering, window-like and stack-like objects):

* `ObjSpec.RWLike S` — *read/write-like* objects: every operation is read-only
  (`ObjSpec.ReadOnly`) or a blind overwrite whose new state and response do not depend on the
  current state (`ObjSpec.Overwrites`); `RWLike B` for a family of base objects;
* `ObjSpec.OverwritesState S` — every operation sets the state independently of the old state
  (historyless objects without read-only operations, e.g. swap objects); responses may depend
  on the old state;
* `ObjSpec.TASLike S` — every operation sets the object to one fixed state (test&set);
* `ObjSpec.Readable S` — some read-only operation returns the whole state.

## Main statements

* `ObjSpec.RWLike.interfering`: read/write-like objects are interfering.
* `ObjSpec.windowLike_one_of_rw`: read/write-like objects are window-like with window `1`.
* `ObjSpec.TASLike.overwritesState`: test&set-like objects overwrite the state.
-/

@[expose] public section

namespace Cslib.SharedMemory

namespace ObjSpec

variable {S : ObjSpec}

/-! ## Read/write-like objects -/

/-- *Read/write-like* objects: every operation is read-only, or a blind overwrite whose new
state and response do not depend on the current state. -/
def RWLike (S : ObjSpec) : Prop := ∀ o, S.ReadOnly o ∨ S.Overwrites o

/-- `RWLike`, unfolded. -/
lemma rwLike_iff :
    S.RWLike ↔ ∀ o, (∀ s, (S.δ s o).1 = s) ∨ ∀ s s', S.δ s o = S.δ s' o := Iff.rfl

/-- Read/write-like objects are interfering: two reads commute, and an overwrite overwrites
every operation. -/
lemma RWLike.interfering (h : S.RWLike) : S.Interfering := by
  intro s o₁ o₂
  rcases h o₁ with h₁ | h₁
  · rcases h o₂ with h₂ | h₂
    · left
      change (S.δ (S.δ s o₁).1 o₂).1 = (S.δ (S.δ s o₂).1 o₁).1
      rw [h₁ s, h₂ s, h₁ s]
    · right; right
      change (S.δ (S.δ s o₁).1 o₂).1 = (S.δ s o₂).1
      rw [h₂ (S.δ s o₁).1 s]
  · right; left
    change (S.δ (S.δ s o₂).1 o₁).1 = (S.δ s o₁).1
    rw [h₁ (S.δ s o₂).1 s]

/-- Read/write-like objects are window-like with window `1`. -/
lemma windowLike_one_of_rw (h : S.RWLike) : S.WindowLike 1 := by
  refine ⟨fun o => (h o).imp id (fun ho s s' => by rw [ho s s']), fun os hne _ hro s s' => ?_⟩
  obtain ⟨o, os, rfl⟩ := List.exists_cons_of_ne_nil hne
  have ho : S.Overwrites o := (h o).resolve_left (hro o List.mem_cons_self)
  simp only [ObjSpec.runOps_cons, ho s s']

/-! ## Objects that overwrite the state -/

/-- Every operation sets the state to a value independent of the old state (a historyless
object all of whose operations are nontrivial, e.g. a swap object). Unlike
`ObjSpec.Overwrites`, the response may depend on the old state. -/
def OverwritesState (S : ObjSpec) : Prop := ∀ o s s', (S.δ s o).1 = (S.δ s' o).1

/-! ## Test&set-like objects -/

/-- An object whose every operation sets it to a fixed state `s₁` (test&set objects: every
`T&S()` sets the bit). -/
def TASLike (S : ObjSpec) : Prop := ∃ s₁, ∀ s o, (S.δ s o).1 = s₁

/-- Test&set-like objects overwrite the state. -/
lemma TASLike.overwritesState (h : S.TASLike) : S.OverwritesState := by
  obtain ⟨s₁, h⟩ := h
  intro o s s'
  rw [h, h]

/-! ## Readable objects -/

/-- `S` is *readable*: some read-only operation returns the current state (its response
determines the state). -/
def Readable (S : ObjSpec) : Prop :=
  ∃ o : S.Op, S.ReadOnly o ∧ Function.Injective fun s => (S.δ s o).2

end ObjSpec

/-- A family of base objects is *read/write-like* if each of them is. -/
def RWLike {ι : Type} (B : ι → ObjSpec) : Prop :=
  ∀ i (o : (B i).Op), (B i).ReadOnly o ∨ (B i).Overwrites o

/-- A family is read/write-like iff each member is. -/
lemma rwLike_iff_forall {ι : Type} {B : ι → ObjSpec} : RWLike B ↔ ∀ i, (B i).RWLike := Iff.rfl

/-! ## The standard objects belong to the classes -/

/-- Registers are read/write-like. -/
lemma register_rwLike (V : Type) (v₀ : V) : (register V v₀).RWLike := by
  intro o
  cases o with
  | read => exact Or.inl fun _ => rfl
  | write v => exact Or.inr fun _ _ => rfl

/-- Families of registers are read/write-like. -/
lemma rwLike_register {ι : Type} {V : ι → Type} (v₀ : ∀ i, V i) :
    RWLike (fun i => register (V i) (v₀ i)) :=
  fun i => register_rwLike (V i) (v₀ i)

/-- Registers are readable. -/
lemma register_readable (V : Type) (v₀ : V) : (register V v₀).Readable :=
  ⟨.read, fun _ => rfl, fun _ _ h => h⟩

/-- Swap objects overwrite the state. -/
lemma swapObj_overwritesState (D : Type) (d₀ : D) : (swapObj D d₀).OverwritesState :=
  fun _ _ _ => rfl

/-- The (non-readable) test&set object is test&set-like. -/
lemma tasObj_tasLike : tasObj.TASLike := ⟨true, fun _ _ => rfl⟩

end Cslib.SharedMemory
