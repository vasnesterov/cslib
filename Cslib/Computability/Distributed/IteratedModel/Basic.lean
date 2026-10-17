/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic

/-!
# Iterated round-based full-information models (protocol-complex view)

A self-contained model of *iterated* wait-free shared-memory computation in the style of
Herlihy–Kozlov–Rajsbaum (*Distributed Computing Through Combinatorial Topology*), as used by
Fraigniaud–Paz–Rajsbaum (PODC 2022) and the asynchronous-complexity literature.

* Processes `P`; a **round pattern** `Pattern P B` says, for every process `i`, which processes'
  writes of the current round `i` collects (`sees i`) and what an optional *black box* object
  returned to `i` (`out i : B`; use `B = Unit` for no box).
* A **model** `Model P A B` gives, for every participating set `I` and every vector of box inputs
  `a : P → A`, the set of admissible patterns `Pat I a` (e.g. immediate snapshot, snapshot,
  immediate snapshot + test&set, …; see `IteratedModel/Patterns.lean`). Box behaviour depends
  only on the participating set and the box inputs ("consistent" boxes).
* **Full information**: the view after `r + 1` rounds is the box output together with the partial
  map `j ↦ view of j after r rounds` restricted to the processes seen (`View`, `step`).
* An **algorithm** with `t` rounds (`Alg`) chooses the box input of each round from the current
  view (`inp`) and decides from the final view (`dec`).
* A **task** (`Task`) is a set of input simplices `(I, x)` (participating set + inputs; only `x` on
  `I` matters) and a relation `Δ I x` of legal outputs (again only values on `I` matter). Δ is not
  required to be a carrier map.
* `Solves M T alg`: for every input simplex and every `t`-round execution in which exactly the
  processes of `I` participate, the decisions of `I` form a legal output. Executions in which some
  processes crash are faces of such executions in all models used here (`Model.Extendable`).
-/

@[expose] public section

namespace Cslib.Iterated

/-- A one-round communication pattern: `sees i` is the set of processes whose writes of this round
process `i` reads, `out i` is the value returned to `i` by the black box of this round. -/
structure Pattern (P B : Type) where
  /-- The processes whose writes of this round a process reads. -/
  sees : P → Finset P
  /-- The value returned to a process by the black box of this round. -/
  out : P → B

/-- An iterated model, possibly augmented with a black-box object with inputs `A` and outputs `B`:
`Pat I a` is the set of admissible one-round patterns when exactly the processes of `I` take part
in the round and process `i` calls the box with input `a i`. -/
structure Model (P A B : Type) where
  /-- The admissible one-round patterns, given the participating set and the box inputs. -/
  Pat : Finset P → (P → A) → Set (Pattern P B)

/-- Full-information views: the view after `0` rounds is the input; the view after `r + 1` rounds is
the box output of round `r + 1` together with the round-`r` views of the processes seen. -/
@[reducible] def View (P X B : Type) : ℕ → Type
  | 0 => X
  | r + 1 => B × (P → Option (View P X B r))

variable {P X Y A B : Type}

/-- Views after one more round with pattern `p`. -/
def step [DecidableEq P] {r : ℕ} (V : P → View P X B r) (p : Pattern P B) :
    P → View P X B (r + 1) :=
  fun i => ((p.out i, fun j => if j ∈ p.sees i then some (V j) else none) :
    B × (P → Option (View P X B r)))

/-- A `t`-round full-information algorithm (Algorithm 1/2 of Fraigniaud–Paz–Rajsbaum): `inp r i v`
is the box input of process `i` in round `r + 1` when its view is `v`, `dec i v` its decision after
`t` rounds. -/
structure Alg (P X A B Y : Type) (t : ℕ) where
  /-- The box input of a process in round `r + 1`, as a function of its view. -/
  inp : (r : ℕ) → P → View P X B r → A
  /-- The decision of a process, as a function of its final view. -/
  dec : P → View P X B t → Y

/-- `Reach M inp I x r V`: `V` is the vector of views after `r` rounds of an execution in which
exactly the processes of `I` participate, starting from inputs `x`. -/
inductive Reach [DecidableEq P] (M : Model P A B) (inp : (r : ℕ) → P → View P X B r → A)
    (I : Finset P) (x : P → X) : (r : ℕ) → (P → View P X B r) → Prop
  /-- After `0` rounds the views are the inputs. -/
  | zero : Reach M inp I x 0 x
  /-- One more round with an admissible pattern. -/
  | succ {r : ℕ} {V : P → View P X B r} (p : Pattern P B) :
      Reach M inp I x r V → p ∈ M.Pat I (fun i => inp r i (V i)) →
      Reach M inp I x (r + 1) (step V p)

/-- A task: input simplices `(I, x)` and the output relation `Δ I x` (a set of output vectors;
only their values on `I` matter). -/
structure Task (P X Y : Type) where
  /-- The input simplices: participating set and inputs. -/
  Inp : Set (Finset P × (P → X))
  /-- The legal output vectors for an input simplex. -/
  Δ : Finset P → (P → X) → Set (P → Y)

/-- `alg` solves `T` in model `M`. -/
def Solves [DecidableEq P] (M : Model P A B) (T : Task P X Y) {t : ℕ} (alg : Alg P X A B Y t) :
    Prop :=
  ∀ I x, (I, x) ∈ T.Inp → ∀ V, Reach M alg.inp I x t V →
    ∃ y ∈ T.Δ I x, ∀ i ∈ I, alg.dec i (V i) = y i

/-- `T` is solvable in `t` rounds in model `M`. -/
def Solvable [DecidableEq P] (M : Model P A B) (T : Task P X Y) (t : ℕ) : Prop :=
  ∃ alg : Alg P X A B Y t, Solves M T alg

/-- `T'` is easier than `T`: fewer inputs, more outputs (on the participating processes). -/
def Task.Easier (T' T : Task P X Y) : Prop :=
  T'.Inp ⊆ T.Inp ∧ ∀ I x, (I, x) ∈ T'.Inp → ∀ y ∈ T.Δ I x, ∃ y' ∈ T'.Δ I x, ∀ i ∈ I, y' i = y i

namespace Model

variable [DecidableEq P] (M : Model P A B)

/-- Every participating process sees itself and only participating processes. -/
def WellFormed : Prop :=
  ∀ I a, ∀ p ∈ M.Pat I a, ∀ i ∈ I, i ∈ p.sees i ∧ p.sees i ⊆ I

/-- The model allows solo executions: in every round, any participating process may run before all
the others, i.e. see only itself. -/
def AllowsSolo : Prop :=
  ∀ I a, ∀ i ∈ I, ∃ p ∈ M.Pat I a, p.sees i = {i}

/-- The box answer of a process that runs solo is determined by its own box input (`b₀ i (a i)`).
This is the "consistency" assumption of Fraigniaud–Paz–Rajsbaum, as far as solo runs are
concerned. -/
def SoloDet (b₀ : P → A → B) : Prop :=
  ∀ I a, ∀ p ∈ M.Pat I a, ∀ i ∈ I, p.sees i = {i} → p.out i = b₀ i (a i)

/-- A round in which only `J ⊆ I` participates is indistinguishable, for `J`, from a round of `I`
(the late processes come last). Equivalently: crash executions are faces of failure-free ones. -/
def Extendable : Prop :=
  ∀ J I, J ⊆ I → ∀ a, ∀ p ∈ M.Pat J a, ∃ p' ∈ M.Pat I a,
    ∀ j ∈ J, p'.sees j = p.sees j ∧ p'.out j = p.out j

end Model

section Lemmas

variable [DecidableEq P] {M : Model P A B}

/-- The view after one more round, unfolded. -/
@[simp] lemma step_apply {r : ℕ} (V : P → View P X B r) (p : Pattern P B) (i : P) :
    step V p i = ((p.out i, fun j => if j ∈ p.sees i then some (V j) else none) :
      B × (P → Option (View P X B r))) := rfl

/-- After `0` rounds, the views are the inputs. -/
lemma reach_zero_iff {inp : (r : ℕ) → P → View P X B r → A} {I : Finset P} {x : P → X}
    {V : P → View P X B 0} : Reach M inp I x 0 V ↔ V = x := by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; exact Reach.zero

/-- The views after `r + 1` rounds come from views after `r` rounds and an admissible pattern. -/
lemma reach_succ_iff {inp : (r : ℕ) → P → View P X B r → A} {I : Finset P} {x : P → X} {r : ℕ}
    {W : P → View P X B (r + 1)} :
    Reach M inp I x (r + 1) W ↔ ∃ V p, Reach M inp I x r V ∧
      p ∈ M.Pat I (fun i => inp r i (V i)) ∧ W = step V p := by
  constructor
  · intro h
    cases h with
    | succ p hV hp => exact ⟨_, p, hV, hp, rfl⟩
  · rintro ⟨V, p, hV, hp, rfl⟩; exact Reach.succ p hV hp

/-- Reachability only depends on the box-input functions of the rounds already executed. -/
lemma Reach.congr_inp {inp inp' : (r : ℕ) → P → View P X B r → A} {I : Finset P} {x : P → X}
    {r : ℕ} {V : P → View P X B r} (h : Reach M inp I x r V)
    (hinp : ∀ s < r, inp s = inp' s) : Reach M inp' I x r V := by
  induction h with
  | zero => exact Reach.zero
  | succ p hV hp ih =>
    refine Reach.succ p (ih fun s hs => hinp s (by omega)) ?_
    rwa [← hinp _ (by omega)]

/-- One-round solvability, unfolded. -/
lemma Solves.one_round {T : Task P X Y} {alg : Alg P X A B Y 1} (h : Solves M T alg)
    {J : Finset P} {x : P → X} (hJ : (J, x) ∈ T.Inp) (p : Pattern P B)
    (hp : p ∈ M.Pat J (fun i => alg.inp 0 i (x i))) :
    ∃ y ∈ T.Δ J x, ∀ i ∈ J, alg.dec i (step (X := X) (B := B) (r := 0) x p i) = y i :=
  h J x hJ _ (Reach.succ p Reach.zero hp)

/-- Monotonicity: an algorithm for a task solves every easier task. -/
lemma Solves.mono {T T' : Task P X Y} {t : ℕ} {alg : Alg P X A B Y t} (h : Solves M T alg)
    (hT : T'.Easier T) : Solves M T' alg := by
  intro I x hI V hV
  obtain ⟨y, hy, hdec⟩ := h I x (hT.1 hI) V hV
  obtain ⟨y', hy', hyy'⟩ := hT.2 I x hI y hy
  exact ⟨y', hy', fun i hi => (hdec i hi).trans (hyy' i hi).symm⟩

/-- Monotonicity: a solvable task stays solvable when it gets easier. -/
lemma Solvable.mono {T T' : Task P X Y} {t : ℕ} (h : Solvable M T t) (hT : T'.Easier T) :
    Solvable M T' t :=
  let ⟨alg, halg⟩ := h; ⟨alg, halg.mono hT⟩

omit [DecidableEq P] in
/-- Every task is as easy as itself. -/
lemma Task.Easier.refl (T : Task P X Y) : T.Easier T :=
  ⟨le_rfl, fun _ _ _ y hy => ⟨y, hy, fun _ _ => rfl⟩⟩

omit [DecidableEq P] in
/-- A convenient sufficient condition for `Easier`: same inputs, pointwise smaller relation. -/
lemma Task.Easier.of_subset {T T' : Task P X Y} (hInp : T'.Inp ⊆ T.Inp)
    (hΔ : ∀ I x, (I, x) ∈ T'.Inp → T.Δ I x ⊆ T'.Δ I x) : T'.Easier T :=
  ⟨hInp, fun I x hI y hy => ⟨y, hΔ I x hI hy, fun _ _ => rfl⟩⟩

end Lemmas

end Cslib.Iterated
