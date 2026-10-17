/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Task
public import Cslib.Computability.Distributed.SharedMemory.Covering

/-!
# Full-information versions of read/write algorithms

A *read/write algorithm* is an `Impl` whose base objects are registers (`RegFamily ι V v₀`). In a
*full-information* algorithm every process writes its *view* — its identifier, its inputs and the
full sequence of values it has read — and the values it reads are views of other processes
(or `⊥`, the initial value). The *full-information version* `I.fullInfo` of a read/write algorithm
`I` runs `I` and additionally maintains views: each register stores the value `I` would store
together with the view of its writer, each process stores its local state of `I` together with
its view. (The paper lets the full-information version recompute `I`'s state from the view; since
`I` is deterministic, `I`'s state is a function of the view, so caching it changes nothing.)

## Main definitions

* `View P In`: views (`mk p hist`, `hist` = inputs `inl x` and reads `inr w`, `w = none` for `⊥`).
* `View.Mentions w q`: the identifier `q` appears in `w` (`q` is the owner of `w` or of a view
  nested in it). "`q` appears in `p`'s view" in the paper.
* `Impl.fullInfo I`, `Impl.fiProj` (forget the views).
* `Impl.FIClean z C`: no register and no process other than `z` mentions `z` in `C`.

## Main results

* `Impl.fullInfo_step`, `Impl.fullInfo_runFrom`, `Impl.fullInfo_run`: `I.fullInfo` has exactly the
  executions of `I` (same labels), and forgetting views maps its configurations to those of `I`.
* `Impl.fullInfo_solves`, `Impl.fullInfo_oneShotOF`, `Impl.fullInfo_obstructionFree`,
  `Impl.fullInfo_waitFree`: the full-information version solves the same tasks with the same
  progress guarantees and the same registers.
* `Impl.fiClean_step`: steps of processes other than `z` preserve `FIClean z`;
  `Impl.fiClean_of_not_invoked`: non-participating processes are mentioned nowhere.
* `Impl.exists_erase`: **causal erasure** — given an execution and a process `z`, there is an
  execution in which `z` does not participate and every process whose final view does not
  mention `z` has exactly the same invocations and responses.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace Cslib.SharedMemory

/-! ### Views -/

/-- Full-information views: owner and history (inputs and read values, `none` = initial value). -/
inductive View (P In : Type) where
  | mk (p : P) (hist : List (In ⊕ Option (View P In)))

namespace View

variable {P In : Type}

/-- The owner of a view. -/
def owner : View P In → P
  | mk p _ => p

/-- The history of a view. -/
def hist : View P In → List (In ⊕ Option (View P In))
  | mk _ h => h

/-- Append an event to a view. -/
def push (v : View P In) (e : In ⊕ Option (View P In)) : View P In := mk v.owner (v.hist ++ [e])

@[simp] lemma owner_mk (p : P) (h : List (In ⊕ Option (View P In))) : (mk p h).owner = p := rfl
@[simp] lemma hist_mk (p : P) (h : List (In ⊕ Option (View P In))) : (mk p h).hist = h := rfl
@[simp] lemma owner_push (v : View P In) (e) : (v.push e).owner = v.owner := rfl

/-- `q` appears in the view: it is the owner of the view or of a view read (transitively). -/
inductive Mentions : View P In → P → Prop
  | self (p : P) (hist : List (In ⊕ Option (View P In))) : Mentions (mk p hist) p
  | read {p : P} {hist : List (In ⊕ Option (View P In))} {w : View P In} {q : P} :
      Sum.inr (some w) ∈ hist → Mentions w q → Mentions (mk p hist) q

lemma mentions_owner (v : View P In) : v.Mentions v.owner := by
  cases v; exact .self _ _

lemma mentions_mk_iff {p q : P} {h : List (In ⊕ Option (View P In))} :
    (mk p h).Mentions q ↔ q = p ∨ ∃ w, Sum.inr (some w) ∈ h ∧ w.Mentions q := by
  constructor
  · intro hm
    cases hm with
    | self => exact Or.inl rfl
    | read hw hq => exact Or.inr ⟨_, hw, hq⟩
  · rintro (rfl | ⟨w, hw, hq⟩)
    · exact .self _ _
    · exact .read hw hq

lemma mentions_push_iff {v : View P In} {e : In ⊕ Option (View P In)} {q : P} :
    (v.push e).Mentions q ↔ v.Mentions q ∨ ∃ w, e = Sum.inr (some w) ∧ w.Mentions q := by
  cases v with
  | mk p h =>
    simp only [push, owner_mk, hist_mk, mentions_mk_iff, List.mem_append, List.mem_singleton]
    constructor
    · rintro (h1 | ⟨w, (hw | hw), hq⟩)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr ⟨w, hw, hq⟩)
      · exact Or.inr ⟨w, hw.symm, hq⟩
    · rintro ((h1 | ⟨w, hw, hq⟩) | ⟨w, rfl, hq⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, Or.inl hw, hq⟩
      · exact Or.inr ⟨w, Or.inr rfl, hq⟩

@[simp] lemma mentions_push_inl {v : View P In} {x : In} {q : P} :
    (v.push (.inl x)).Mentions q ↔ v.Mentions q := by
  simp [mentions_push_iff]

@[simp] lemma mentions_push_inr_none {v : View P In} {q : P} :
    (v.push (.inr none)).Mentions q ↔ v.Mentions q := by
  simp [mentions_push_iff]

@[simp] lemma mentions_push_inr_some {v w : View P In} {q : P} :
    (v.push (.inr (some w))).Mentions q ↔ v.Mentions q ∨ w.Mentions q := by
  simp [mentions_push_iff]

/-- A read value mentions `q` (`⊥` mentions nobody). -/
def OMentions : Option (View P In) → P → Prop
  | none, _ => False
  | some w, q => w.Mentions q

@[simp] lemma oMentions_none (q : P) : OMentions (none : Option (View P In)) q ↔ False := Iff.rfl
@[simp] lemma oMentions_some (w : View P In) (q : P) : OMentions (some w) q ↔ w.Mentions q :=
  Iff.rfl

lemma mentions_push_inr {v : View P In} {w : Option (View P In)} {q : P} :
    (v.push (.inr w)).Mentions q ↔ v.Mentions q ∨ OMentions w q := by
  cases w <;> simp

end View

/-! ### Read/write algorithms and their full-information versions -/

/-- A family of read/write registers over values `V` (initial values come from `Impl.memInit`). -/
abbrev RegFamily (ι V : Type) (v₀ : V) : ι → ObjSpec := fun _ => register V v₀

variable {A : ObjSpec} {ι V P L : Type} {v₀ : V}

namespace Impl

/-- The full-information version of a read/write algorithm. -/
def fullInfo (I : Impl A (RegFamily ι V v₀) P L) :
    Impl A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op) where
  memInit i := (I.memInit i, none)
  locInit p := (I.locInit p, .mk p [])
  invoke p l o := (I.invoke p l.1 o, l.2.push (.inl o))
  act p l := match I.act p l.1 with
    | .access i .read k => .access i .read (fun w => (k w.1, l.2.push (.inr w.2)))
    | .access i (.write v) k => .access i (.write (v, some l.2)) (fun w => (k w.1, l.2))
    | .ret r l' => .ret r (l', l.2)
  allowed := I.allowed

/-- Configurations of the full-information version. -/
abbrev FIConfig (A : ObjSpec) (ι V P L : Type) (v₀ : V) : Type :=
  Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)

/-- Forget the views. -/
def fiProj (C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)) :
    Config A (RegFamily ι V v₀) P L :=
  ⟨fun p => (C.loc p).1, C.pend, fun i => (C.mem i).1⟩

@[simp] lemma fiProj_loc (C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P
    (L × View P A.Op)) (p : P) : (fiProj C).loc p = (C.loc p).1 := rfl
@[simp] lemma fiProj_pend (C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P
    (L × View P A.Op)) : (fiProj C).pend = C.pend := rfl
@[simp] lemma fiProj_mem (C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P
    (L × View P A.Op)) (i : ι) : (fiProj C).mem i = (C.mem i).1 := rfl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A (RegFamily ι V v₀) P L)

omit [DecidableEq P] [DecidableEq ι] in
lemma fullInfo_initCfg : fiProj I.fullInfo.initCfg = I.initCfg := rfl

/-- One step of the full-information version, projected, is a step of `I`. -/
theorem fullInfo_step
    (C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op))
    (ℓ : Label P A) : (I.fullInfo.step C ℓ).map fiProj = I.step (fiProj C) ℓ := by
  classical
  cases ℓ with
  | inv p o =>
    by_cases h : C.pend p = none ∧ I.allowed p o
    · simp only [step, h, fullInfo, and_self, ↓reduceIte, Option.map_some, fiProj,
        Option.some.injEq, Config.mk.injEq, and_true]
      funext q; by_cases hq : q = p <;> simp [hq]
    · simp [step, fullInfo, h]
  | tau p =>
    by_cases h : C.pend p = none
    · simp [step, h]
    · rcases hact : I.act p (C.loc p).1 with ⟨i, o, k⟩ | ⟨r, l'⟩
      · cases o with
        | read =>
          simp only [step, h, ↓reduceIte, fullInfo, hact, Function.update_eq_self,
            Option.map_some, fiProj, Option.some.injEq, Config.mk.injEq, and_self, and_true]
          funext q; by_cases hq : q = p <;> simp [hq]
        | write v =>
          simp only [step, h, ↓reduceIte, fullInfo, hact, Option.map_some, fiProj,
            Option.some.injEq, Config.mk.injEq, true_and]
          refine ⟨?_, ?_⟩ <;>
            (first
              | (funext q; by_cases hq : q = p <;> simp [hq])
              | (funext q; by_cases hq : q = i <;> simp [hq]))
      · simp [step, fullInfo, h, hact]
  | ret p r =>
    by_cases h : C.pend p = none
    · simp [step, h]
    · rcases hact : I.act p (C.loc p).1 with ⟨i, o, k⟩ | ⟨r', l'⟩
      · cases o with
        | read => simp [step, fullInfo, h, hact]
        | write v => simp [step, fullInfo, h, hact]
      · by_cases hr : r = r'
        · simp only [step, h, ↓reduceIte, fullInfo, hact, hr, Option.map_some, fiProj,
            Option.some.injEq, Config.mk.injEq, and_self, and_true]
          funext q; by_cases hq : q = p <;> simp [hq]
        · simp [step, fullInfo, h, hact, hr]

theorem fullInfo_runFrom
    (C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op))
    (α : List (Label P A)) : (I.fullInfo.runFrom C α).map fiProj = I.runFrom (fiProj C) α := by
  induction α generalizing C with
  | nil => rfl
  | cons ℓ α ih =>
    simp only [runFrom_cons]
    rw [← fullInfo_step]
    cases h : I.fullInfo.step C ℓ with
    | none => rfl
    | some C' => simp [ih]

theorem fullInfo_run (α : List (Label P A)) : (I.fullInfo.run α).map fiProj = I.run α :=
  I.fullInfo_runFrom _ α

lemma fullInfo_run_some {α : List (Label P A)}
    {C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)}
    (h : I.fullInfo.run α = some C) : I.run α = some (fiProj C) := by
  rw [← fullInfo_run, h]; rfl

lemma fullInfo_run_of_run {α : List (Label P A)} {D : Config A (RegFamily ι V v₀) P L}
    (h : I.run α = some D) : ∃ C, I.fullInfo.run α = some C ∧ fiProj C = D := by
  have := I.fullInfo_run α
  rw [h] at this
  cases h' : I.fullInfo.run α with
  | none => rw [h'] at this; cases this
  | some C => rw [h'] at this; exact ⟨C, rfl, Option.some.inj this⟩

lemma fullInfo_valid_iff {α : List (Label P A)} : I.fullInfo.Valid α ↔ I.Valid α := by
  constructor
  · rintro ⟨C, hC⟩; exact ⟨_, I.fullInfo_run_some hC⟩
  · rintro ⟨D, hD⟩; obtain ⟨C, hC, -⟩ := I.fullInfo_run_of_run hD; exact ⟨C, hC⟩

omit [DecidableEq P] [DecidableEq ι] in
lemma fullInfo_nextLabel
    (C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op))
    (p : P) : I.fullInfo.nextLabel C p = I.nextLabel (fiProj C) p := by
  simp only [nextLabel, fiProj_loc]
  rcases hact : I.act p (C.loc p).1 with ⟨i, o, k⟩ | ⟨r, l'⟩
  · cases o <;> simp [fullInfo, hact]
  · simp [fullInfo, hact]

lemma fullInfo_soloStep (p : P)
    (C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)) :
    fiProj (I.fullInfo.soloStep p C) = I.soloStep p (fiProj C) := by
  by_cases h : C.pend p = none
  · simp [soloStep, h]
  · obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 (I.fullInfo.step_nextLabel_isSome C p h)
    have h2 := I.fullInfo_step C (I.fullInfo.nextLabel C p)
    rw [hC', fullInfo_nextLabel] at h2
    simp only [soloStep, fiProj_pend, h, ↓reduceIte, hC', Option.getD_some]
    rw [← h2]; rfl

lemma fullInfo_iterate_soloStep (p : P)
    (C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op))
    (n : ℕ) : fiProj ((I.fullInfo.soloStep p)^[n] C) = (I.soloStep p)^[n] (fiProj C) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih,
      fullInfo_soloStep]

lemma fullInfo_oneShotOF (h : I.OneShotOF) : I.fullInfo.OneShotOF := by
  intro α C p hα h1 hp
  obtain ⟨k, hk⟩ := h α (fiProj C) p (I.fullInfo_run_some hα) h1 hp
  exact ⟨k, by rw [← fiProj_pend, I.fullInfo_iterate_soloStep]; exact hk⟩

lemma fullInfo_obstructionFree (h : I.ObstructionFree) : I.fullInfo.ObstructionFree := by
  rintro C p ⟨α, hα⟩ hp
  obtain ⟨k, hk⟩ := h (fiProj C) p ⟨α, I.fullInfo_run_some hα⟩ hp
  exact ⟨k, by rw [← fiProj_pend, I.fullInfo_iterate_soloStep]; exact hk⟩

lemma fullInfo_waitFree (h : I.WaitFree) : I.fullInfo.WaitFree := by
  intro e p n hpend
  let e' : I.InfExec := ⟨fun m => fiProj (e.cfg m), e.lbl, by rw [e.cfg_zero]; rfl, fun m => by
    have := I.fullInfo_step (e.cfg m) (e.lbl m)
    rw [e.step_eq] at this; exact this.symm⟩
  exact h e' p n hpend

/-! ### Views along executions -/

/-- What a step of the full-information version does to the memory and to views. -/
lemma fullInfo_step_cases
    {C C' : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)}
    {ℓ : Label P A} (h : I.fullInfo.step C ℓ = some C') :
    (∀ q, q ≠ ℓ.proc → C'.loc q = C.loc q) ∧
    ((C'.mem = C.mem ∧ ∃ x, (C'.loc ℓ.proc).2 = (C.loc ℓ.proc).2.push (.inl x)) ∨
     (C'.mem = C.mem ∧ (C'.loc ℓ.proc).2 = (C.loc ℓ.proc).2) ∨
     (∃ i, C'.mem = C.mem ∧ (C'.loc ℓ.proc).2 = (C.loc ℓ.proc).2.push (.inr (C.mem i).2)) ∨
     (∃ i v, C'.mem = Function.update C.mem i (v, some (C.loc ℓ.proc).2) ∧
        (C'.loc ℓ.proc).2 = (C.loc ℓ.proc).2)) := by
  refine ⟨fun q hq => (step_other h (Ne.symm hq)).1, ?_⟩
  classical
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, -, h3, h4⟩ := step_inv h
    exact Or.inl ⟨h4, o, by simp [h3, fullInfo, Label.proc]⟩
  | tau p =>
    simp only [Label.proc]
    by_cases hp : C.pend p = none
    · simp [step, hp] at h
    · rcases hact : I.act p (C.loc p).1 with ⟨i, o, k⟩ | ⟨r, l'⟩
      · cases o with
        | read =>
          simp only [step, hp, ↓reduceIte, fullInfo, hact, Function.update_eq_self,
            Option.some.injEq] at h
          subst h
          exact Or.inr (Or.inr (Or.inl ⟨i, by simp, by simp⟩))
        | write v =>
          simp only [step, hp, ↓reduceIte, fullInfo, hact, Option.some.injEq] at h; subst h
          exact Or.inr (Or.inr (Or.inr ⟨i, v, by simp, by simp⟩))
      · simp [step, fullInfo, hp, hact] at h
  | ret p r =>
    obtain ⟨-, -, h2, l, hact, hl⟩ := step_ret h
    simp only [Label.proc]
    refine Or.inr (Or.inl ⟨h2, ?_⟩)
    rw [hl]
    simp only [Function.update_self]
    rcases hact' : I.act p (C.loc p).1 with ⟨i, o, k⟩ | ⟨r', l'⟩
    · cases o <;> simp [fullInfo, hact'] at hact
    · simp only [fullInfo, hact', Action.ret.injEq] at hact
      rw [← hact.2]

lemma fullInfo_step_mentions_mono
    {C C' : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)}
    {ℓ : Label P A} (h : I.fullInfo.step C ℓ = some C') {x z : P}
    (hx : (C.loc x).2.Mentions z) : (C'.loc x).2.Mentions z := by
  obtain ⟨h1, h2⟩ := I.fullInfo_step_cases h
  by_cases hxp : x = ℓ.proc
  · subst hxp
    rcases h2 with ⟨-, e, he⟩ | ⟨-, he⟩ | ⟨i, -, he⟩ | ⟨i, v, -, he⟩ <;> rw [he] <;>
      simp [View.mentions_push_iff, hx]
  · rw [h1 x hxp]; exact hx

lemma fullInfo_runFrom_mentions_mono
    {C C' : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)}
    {β : List (Label P A)} (h : I.fullInfo.runFrom C β = some C') {x z : P}
    (hx : (C.loc x).2.Mentions z) : (C'.loc x).2.Mentions z := by
  induction β generalizing C with
  | nil => simp only [runFrom_nil, Option.some.injEq] at h; subst h; exact hx
  | cons ℓ β ih =>
    simp only [runFrom_cons] at h
    cases hs : I.fullInfo.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      exact ih h (I.fullInfo_step_mentions_mono hs hx)

/-- Every process owns its view. -/
def FIOwners (C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P
    (L × View P A.Op)) : Prop := ∀ x, (C.loc x).2.owner = x

omit [DecidableEq P] [DecidableEq ι] in
lemma fiOwners_init : FIOwners I.fullInfo.initCfg := fun _ => rfl

lemma fullInfo_step_owners
    {C C' : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)}
    {ℓ : Label P A} (h : I.fullInfo.step C ℓ = some C') (hC : FIOwners C) : FIOwners C' := by
  obtain ⟨h1, h2⟩ := I.fullInfo_step_cases h
  intro x
  by_cases hxp : x = ℓ.proc
  · subst hxp
    rcases h2 with ⟨-, e, he⟩ | ⟨-, he⟩ | ⟨i, -, he⟩ | ⟨i, v, -, he⟩ <;> rw [he] <;> simp [hC _]
  · rw [h1 x hxp]; exact hC x

lemma fullInfo_run_owners {α : List (Label P A)}
    {C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)}
    (h : I.fullInfo.run α = some C) : FIOwners C := by
  suffices ∀ (β : List (Label P A)) C₀ C, FIOwners C₀ → I.fullInfo.runFrom C₀ β = some C →
      FIOwners C from this α _ C (I.fiOwners_init) h
  intro β
  induction β with
  | nil => intro C₀ C h0 h; simp only [runFrom_nil, Option.some.injEq] at h; subst h; exact h0
  | cons ℓ β ih =>
    intro C₀ C h0 h
    simp only [runFrom_cons] at h
    cases hs : I.fullInfo.step C₀ ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      exact ih C₁ C (I.fullInfo_step_owners hs h0) h

lemma fullInfo_run_mentions_self {α : List (Label P A)}
    {C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)}
    (h : I.fullInfo.run α = some C) (x : P) : (C.loc x).2.Mentions x := by
  have := (C.loc x).2.mentions_owner; rwa [I.fullInfo_run_owners h x] at this

/-- `z` is mentioned by no register and by no process other than itself. -/
def FIClean (z : P) (C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P
    (L × View P A.Op)) : Prop :=
  (∀ i, ¬ View.OMentions (C.mem i).2 z) ∧ ∀ x, x ≠ z → ¬ (C.loc x).2.Mentions z

/-- Steps of processes other than `z` keep `z` unmentioned. -/
lemma fiClean_step {z : P}
    {C C' : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)}
    {ℓ : Label P A} (h : I.fullInfo.step C ℓ = some C') (hz : ℓ.proc ≠ z) (hC : FIClean z C) :
    FIClean z C' := by
  obtain ⟨h1, h2⟩ := I.fullInfo_step_cases h
  have hp := hC.2 ℓ.proc hz
  refine ⟨fun j => ?_, fun x hx => ?_⟩
  · rcases h2 with ⟨hm, -⟩ | ⟨hm, -⟩ | ⟨i, hm, -⟩ | ⟨i, v, hm, -⟩
    · rw [hm]; exact hC.1 j
    · rw [hm]; exact hC.1 j
    · rw [hm]; exact hC.1 j
    · rw [hm]
      by_cases hj : j = i
      · subst hj; simpa using hp
      · rw [Function.update_of_ne hj]; exact hC.1 j
  · by_cases hxp : x = ℓ.proc
    · subst hxp
      rcases h2 with ⟨-, e, he⟩ | ⟨-, he⟩ | ⟨i, -, he⟩ | ⟨i, v, -, he⟩ <;> rw [he]
      · simpa using hp
      · exact hp
      · rw [View.mentions_push_inr]; exact fun h => h.elim hp (hC.1 i)
      · exact hp
    · rw [h1 x hxp]; exact hC.2 x hx

lemma fiClean_runFrom {z : P}
    {C C' : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)}
    {β : List (Label P A)} (h : I.fullInfo.runFrom C β = some C') (hz : ∀ ℓ ∈ β, ℓ.proc ≠ z)
    (hC : FIClean z C) : FIClean z C' := by
  induction β generalizing C with
  | nil => simp only [runFrom_nil, Option.some.injEq] at h; subst h; exact hC
  | cons ℓ β ih =>
    simp only [runFrom_cons] at h
    cases hs : I.fullInfo.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      exact ih h (fun ℓ' hℓ' => hz ℓ' (by simp [hℓ']))
        (I.fiClean_step hs (hz ℓ (by simp)) hC)

omit [DecidableEq P] [DecidableEq ι] in
lemma fiClean_init (z : P) : FIClean z I.fullInfo.initCfg := by
  refine ⟨fun i => by simp [initCfg, fullInfo], fun x hx => ?_⟩
  simp only [initCfg, fullInfo]
  rw [View.mentions_mk_iff]
  rintro (h | ⟨w, hw, -⟩)
  · exact hx h.symm
  · simp at hw

/-- A process that has not invoked anything is mentioned nowhere. -/
lemma fiClean_of_not_invoked {α : List (Label P A)}
    {C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)}
    (h : I.fullInfo.run α = some C) {z : P} (hz : opsOf α z = []) : FIClean z C :=
  I.fiClean_runFrom h (proc_ne_of_opsOf_eq_nil _ h hz) (I.fiClean_init z)

/-! ### Causal erasure -/

omit [DecidableEq P] [DecidableEq ι] in
/-- The shape of the actions of the full-information version: reads append the value read to the
view, writes store the writer's view. -/
lemma fullInfo_act_access {x : P} {l : L × View P A.Op} {i : ι}
    {o : RWOp (V × Option (View P A.Op))} {k : V × Option (View P A.Op) → L × View P A.Op}
    (h : I.fullInfo.act x l = .access i o k) :
    (o = .read ∧ ∀ w, (k w).2 = l.2.push (.inr w.2)) ∨
      (∃ v, o = .write (v, some l.2) ∧ ∀ w, (k w).2 = l.2) := by
  rcases hI : I.act x l.1 with ⟨i', o', k'⟩ | ⟨r', l'⟩
  · cases o' with
    | read =>
      simp only [fullInfo, hI, Action.access.injEq] at h
      obtain ⟨rfl, h1, h2⟩ := h
      cases h1; cases h2
      exact Or.inl ⟨rfl, fun w => rfl⟩
    | write v =>
      simp only [fullInfo, hI, Action.access.injEq] at h
      obtain ⟨rfl, h1, h2⟩ := h
      cases h1; cases h2
      exact Or.inr ⟨v, rfl, fun w => rfl⟩
  · simp [fullInfo, hI] at h

omit [DecidableEq P] [DecidableEq ι] in
/-- A process covering a register in the full-information version covers it in `I`. -/
lemma fullInfo_covers {C : FIConfig A ι V P L v₀} {p : P} {i : ι}
    (h : I.fullInfo.Covers C p i) : I.Covers (fiProj C) p i := by
  obtain ⟨hp, o, k, hact, hov⟩ := h
  refine ⟨hp, ?_⟩
  rcases hI : I.act p (C.loc p).1 with ⟨i', o', k'⟩ | ⟨r', l'⟩
  · cases o' with
    | read =>
      simp only [fullInfo, hI, Action.access.injEq] at hact
      obtain ⟨rfl, h1, -⟩ := hact
      cases h1
      exfalso
      have := hov ((C.mem i').1, none) ((C.mem i').1, some (.mk p []))
      simp at this
    | write v =>
      simp only [fullInfo, hI, Action.access.injEq] at hact
      obtain ⟨rfl, -, -⟩ := hact
      exact ⟨.write v, k', by simpa using hI, register_write_overwrites _ _⟩
  · simp [fullInfo, hI] at hact

omit [DecidableEq P] [DecidableEq ι] in
/-- Every access of the full-information version is a read (read-only) or a write (overwrite). -/
lemma fullInfo_access_readOnly {x : P} {l : L × View P A.Op} {i : ι}
    {o : RWOp (V × Option (View P A.Op))} {k : V × Option (View P A.Op) → L × View P A.Op}
    (h : I.fullInfo.act x l = .access i o k)
    (hov : ¬ (RegFamily ι (V × Option (View P A.Op)) (v₀, none) i).Overwrites o) :
    (RegFamily ι (V × Option (View P A.Op)) (v₀, none) i).ReadOnly o := by
  rcases I.fullInfo_act_access h with ⟨rfl, -⟩ | ⟨v, rfl, -⟩
  · exact register_read_readOnly _
  · exact absurd (register_write_overwrites _ _) hov

lemma fullInfo_solves {T : Task P} [Inhabited T.Out]
    {I : Impl (taskObj T.In T.Out) (RegFamily ι V v₀) P L} (h : I.Solves T) :
    I.fullInfo.Solves T := fun α hα h1 => h α ((I.fullInfo_valid_iff).1 hα) h1

variable (z : P)

open Classical in
/-- Erase from an execution every step after which the view of the stepping process mentions `z`:
the causal future of `z` (including all steps of `z` itself). -/
noncomputable def fiErase :
    Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op) →
      List (Label P A) → List (Label P A)
  | _, [] => []
  | C, ℓ :: β => match I.fullInfo.step C ℓ with
    | some C' => (if (C'.loc ℓ.proc).2.Mentions z then [] else [ℓ]) ++ fiErase C' β
    | none => []

/-- The relation between a configuration of the original execution and of the erased one:
processes and registers that do not mention `z` are the same. -/
structure FIRel (C D : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P
    (L × View P A.Op)) : Prop where
  loc : ∀ x, ¬ (C.loc x).2.Mentions z → C.loc x = D.loc x ∧ C.pend x = D.pend x
  mem : ∀ i, ¬ View.OMentions (C.mem i).2 z → C.mem i = D.mem i

theorem fiErase_spec : ∀ (β : List (Label P A))
    (C D C' : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)),
    FIOwners C → FIRel z C D → I.fullInfo.runFrom C β = some C' →
    ∃ D', I.fullInfo.runFrom D (I.fiErase z C β) = some D' ∧ FIRel z C' D' ∧
      opsOf (I.fiErase z C β) z = [] ∧
      (∀ x, ¬ (C'.loc x).2.Mentions z →
        opsOf (I.fiErase z C β) x = opsOf β x ∧ respsOf (I.fiErase z C β) x = respsOf β x) ∧
      ∀ x, (opsOf (I.fiErase z C β) x).Sublist (opsOf β x) := by
  classical
  intro β
  induction β with
  | nil =>
    intro C D C' _ hR h
    simp only [runFrom_nil, Option.some.injEq] at h; subst h
    exact ⟨D, rfl, hR, rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ => List.Sublist.refl _⟩
  | cons ℓ β ih =>
    intro C D C' hO hR h
    simp only [runFrom_cons] at h
    cases hs : I.fullInfo.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      have hO₁ := I.fullInfo_step_owners hs hO
      have hcases := I.fullInfo_step_cases hs
      have hdef : I.fiErase z C (ℓ :: β) =
          (if (C₁.loc ℓ.proc).2.Mentions z then [] else [ℓ]) ++ I.fiErase z C₁ β := by
        simp [fiErase, hs]
      by_cases hk : (C₁.loc ℓ.proc).2.Mentions z
      · -- the step is erased
        have hR₁ : FIRel z C₁ D := by
          refine ⟨fun y hy => ?_, fun j hj => ?_⟩
          · have hyx : y ≠ ℓ.proc := fun e => hy (e ▸ hk)
            rw [hcases.1 y hyx, (step_other hs (Ne.symm hyx)).2] at *
            exact hR.loc y hy
          · rcases hcases.2 with ⟨hm, -⟩ | ⟨hm, -⟩ | ⟨i, hm, -⟩ | ⟨i, v, hm, hv⟩
            · rw [hm] at hj ⊢; exact hR.mem j hj
            · rw [hm] at hj ⊢; exact hR.mem j hj
            · rw [hm] at hj ⊢; exact hR.mem j hj
            · by_cases hji : j = i
              · subst hji; rw [hm] at hj; simp [← hv, hk] at hj
              · rw [hm, Function.update_of_ne hji] at hj ⊢; exact hR.mem j hj
        obtain ⟨D', h1, h2, h3, h4, h5⟩ := ih C₁ D C' hO₁ hR₁ h
        refine ⟨D', by rw [hdef]; simpa [hk] using h1, h2, by rw [hdef]; simpa [hk] using h3,
          fun x hx => ?_, fun x => ?_⟩
        · have hxl : ℓ.proc ≠ x := by
            rintro rfl; exact hx (I.fullInfo_runFrom_mentions_mono h hk)
          rw [hdef]; simp only [hk, ↓reduceIte, List.nil_append, opsOf_cons, respsOf_cons,
            Label.invOf_eq_none_of_proc_ne hxl, Label.retOf_eq_none_of_proc_ne hxl,
            Option.toList_none, List.nil_append]
          exact h4 x hx
        · rw [hdef]; simp only [hk, ↓reduceIte, List.nil_append, opsOf_cons]
          exact (h5 x).trans (List.sublist_append_right _ _)
      · -- the step is kept
        obtain ⟨x, hx⟩ : ∃ x, ℓ.proc = x := ⟨_, rfl⟩
        rw [hx] at hk
        have hx0 : ¬ (C.loc x).2.Mentions z := fun h0 =>
          hk (I.fullInfo_step_mentions_mono hs h0)
        obtain ⟨hl, hp⟩ := hR.loc _ hx0
        have hmem : ℓ = .tau x → ∀ i o k, I.fullInfo.act x (C.loc x) = .access i o k →
            ¬ (RegFamily ι (V × Option (View P A.Op)) (v₀, none) i).Overwrites o →
            C.mem i = D.mem i := by
          intro hτ i o k hact hov
          rcases I.fullInfo_act_access hact with ⟨rfl, hk'⟩ | ⟨v, rfl, -⟩
          · apply hR.mem i
            intro hmi
            apply hk
            subst hτ
            obtain ⟨-, -, i', o', k', hact', -, hl'⟩ := step_tau hs
            rw [hact] at hact'
            simp only [Action.access.injEq] at hact'
            obtain ⟨rfl, ho, hkk⟩ := hact'
            cases ho; cases hkk
            rw [hl', Function.update_self, hk', View.mentions_push_inr]
            exact Or.inr hmi
          · exact absurd (register_write_overwrites _ _) hov
        obtain ⟨D₁, hD₁, hl₁, hp₁, hm₁⟩ := step_local hl hp hx hmem hs
        have hR₁ : FIRel z C₁ D₁ := by
          refine ⟨fun y hy => ?_, fun j hj => ?_⟩
          · by_cases hyx : y = x
            · subst hyx; exact ⟨hl₁, hp₁⟩
            · have e1 := step_other hs (hx ▸ Ne.symm hyx : ℓ.proc ≠ y)
              have e2 := step_other hD₁ (hx ▸ Ne.symm hyx : ℓ.proc ≠ y)
              rw [e1.1] at hy
              rw [e1.1, e1.2, e2.1, e2.2]; exact hR.loc y hy
          · rcases hm₁ j with ⟨e1, e2⟩ | e
            · rw [e1] at hj ⊢; rw [e2]; exact hR.mem j hj
            · exact e
        obtain ⟨D', h1, h2, h3, h4, h5⟩ := ih C₁ D₁ C' hO₁ hR₁ h
        have hxz : ℓ.proc ≠ z := by
          rintro rfl; rw [← hx] at hk; exact hk (by
            have := (C₁.loc ℓ.proc).2.mentions_owner; rwa [hO₁ ℓ.proc] at this)
        refine ⟨D', ?_, h2, ?_, fun y hy => ?_, fun y => ?_⟩
        · rw [hdef, hx]; simp only [hk, ↓reduceIte, List.singleton_append, runFrom_cons, hD₁,
            Option.bind_some]; exact h1
        · rw [hdef, hx]; simp only [hk, ↓reduceIte, List.singleton_append, opsOf_cons,
            Label.invOf_eq_none_of_proc_ne hxz, Option.toList_none, List.nil_append]; exact h3
        · rw [hdef, hx]; simp only [hk, ↓reduceIte, List.singleton_append, opsOf_cons,
            respsOf_cons]
          rw [(h4 y hy).1, (h4 y hy).2]; exact ⟨rfl, rfl⟩
        · rw [hdef, hx]; simp only [hk, ↓reduceIte, List.singleton_append, opsOf_cons]
          exact (h5 y).append_left _

/-- **Causal erasure.** Given an execution of the full-information version and a process `z`, there
is an execution in which `z` does not participate, every process whose final view does not mention
`z` has the same invocations and responses, and nobody invokes more than before. -/
theorem fullInfo_exists_erase {α : List (Label P A)}
    {C : Config A (RegFamily ι (V × Option (View P A.Op)) (v₀, none)) P (L × View P A.Op)}
    (hα : I.fullInfo.run α = some C) :
    ∃ α', I.fullInfo.Valid α' ∧ opsOf α' z = [] ∧
      (∀ x, ¬ (C.loc x).2.Mentions z → opsOf α' x = opsOf α x ∧ respsOf α' x = respsOf α x) ∧
      ∀ x, (opsOf α' x).Sublist (opsOf α x) := by
  obtain ⟨D', h1, -, h3, h4, h5⟩ := I.fiErase_spec z α _ _ C (I.fiOwners_init)
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩ hα
  exact ⟨_, ⟨D', h1⟩, h3, h4, h5⟩

end Impl

end Cslib.SharedMemory
