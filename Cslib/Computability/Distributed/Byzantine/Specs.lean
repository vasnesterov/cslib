/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.LockStep.Agreement
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Specifications of agreement problems

Agreement problems are specified by a predicate on the inputs `inp : P → I` of the processes, the
set `H : Set P` of honest (correct) processes, and the outputs of the honest processes. Papers
phrase the outputs in two ways, and this file has both:

* a *decision relation* `dec : P → O → Prop` ("`p` decides `o`"), as in CSLib's lock-step
  `Cslib.Byzantine.LockStep.Spec`; a property of decision relations is a `LockStep.Spec`;
* an *output function* `out : P → O`, for one-shot sub-protocols whose outputs are only
  constrained by their specification (graded consensus inside phase king, Proxcensus, …).

A paper with a faulty set `F : Finset P` uses `H = (↑F)ᶜ`; then `p ∈ H` is definitionally
`p ∉ F`. The names are generic, so they live in the namespace `Cslib.Byzantine.Problem` (write
`Problem.Agreement`, or `open Cslib.Byzantine.Problem`).

## Main definitions

Decision relations:
* `Termination H dec`, `StrongUnanimity inp H dec`, `Agreement H dec`: the three clauses of
  Byzantine agreement; `LockStep.BA` is their conjunction (`ba_iff`, by `Iff.rfl`).
* `ofOut S`: the `LockStep.Spec` "every honest process decides, and every choice of honest
  decisions satisfies the output-function specification `S`".
* `Gradecast top Cons snd`: gradecast with sender `snd`, grades in any type with top grade `top`,
  and graded consistency `Cons`.
* `SenderValidity inp H s dec`: an honest sender's input is decided by every honest process
  (validity of Byzantine broadcast and gradecast).
* `VectorValidity inp H dec`: honest decision vectors carry the honest inputs (validity of
  interactive consistency).
* `InputValidity inp H dec`: honest decisions are honest inputs (validity of consensus with
  "honest-input" validity).
* `InRange inp H v`: `v` lies between two honest inputs.
* `RangeValidity inp H dec`: every honest decision is `InRange` (validity of approximate
  agreement).
* `EpsAgreement ε H dec`: any two honest decisions are at distance at most `ε`.
* `ApproxAgreement ε`: `ε`-approximate agreement, i.e. termination, range validity and
  `ε`-agreement.

Output functions:
* `Consensus inp H out`: agreement and strong unanimity.
* `GradedConsensus inp H out`: graded consensus (graded agreement) with a binary grade.
* `Proxcensus s inp H out`: `s`-slot Proxcensus (grades `0, …, ⌊(s - 1)/2⌋`).

## Main statements

* `ba_iff`: CSLib's `LockStep.BA` is termination, strong unanimity and agreement.
* `bb_iff`, `ic_iff`, `weakAgreement_iff`: CSLib's lock-step `BB`, `IC` and `WeakAgreement` are
  conjunctions of these clauses (by `Iff.rfl`).
* `InRange.of_le_of_le`, `InRange.eq_of_forall_eq`, `inRange_iff_exists`: basic facts on ranges.
* `inRange_iff_forall_mem_Icc`: for finitely many honest processes, the honest range is the
  intersection of all intervals containing the honest inputs.
* `gradedConsensus_iff`, `binaryGradecast_iff`: the specifications in their usual unfolded form.

The phase-king lemmas built on graded consensus are in
`Cslib.Computability.Distributed.Byzantine.KingPhase`.
-/

@[expose] public section

namespace Cslib.Byzantine.Problem

variable {P I O V G : Type*}

/-! ### Decision relations -/

section Relations

variable (inp : P → V) (H : Set P) (dec : P → O → Prop)

/-- **Termination**: every honest process decides. -/
def Termination : Prop := ∀ p ∈ H, ∃ o, dec p o

/-- **Strong unanimity** (strong validity): if all honest inputs are `v`, every honest process
decides `v`. -/
def StrongUnanimity (dec : P → V → Prop) : Prop := ∀ v, (∀ p ∈ H, inp p = v) → ∀ p ∈ H, dec p v

/-- **Agreement**: any two decisions of honest processes coincide. -/
def Agreement : Prop := ∀ p ∈ H, ∀ q ∈ H, ∀ v w, dec p v → dec q w → v = w

/-- CSLib's lock-step Byzantine agreement is termination, strong unanimity and agreement. -/
theorem ba_iff (dec : P → V → Prop) :
    LockStep.BA inp H dec ↔ Termination H dec ∧ StrongUnanimity inp H dec ∧ Agreement H dec :=
  Iff.rfl

/-- The lock-step specification of an output-function specification `S`: every honest process
decides, and `S` holds for every output function that picks a decision of each honest process. -/
def ofOut (S : (P → I) → Set P → (P → O) → Prop) : LockStep.Spec P I O := fun x H dec =>
  Termination H dec ∧ ∀ out : P → O, (∀ p ∈ H, dec p (out p)) → S x H out

end Relations

/-! ### Gradecast -/

/-- **Gradecast** with sender `snd`, grades in `G` with top grade `top` and graded consistency
`Cons`: every honest process decides (termination); if the sender is honest, every honest process
outputs the sender's input with grade `top` (validity); and the outputs `(v, g)`, `(w, g')` of
any two honest processes satisfy `Cons v g w g'` (consistency). With binary grades,
`Cons v g w _ := g = true → v = w` (`BinaryGradecast`); with grades `0, 1, 2`,
`Cons v g w g' := g ≤ g' + 1 ∧ (0 < g → 0 < g' → v = w)`. -/
def Gradecast (top : G) (Cons : V → G → V → G → Prop) (snd : P) : LockStep.Spec P V (V × G) :=
  fun x H dec =>
    Termination H dec ∧ (snd ∈ H → ∀ p ∈ H, dec p (x snd, top)) ∧
      ∀ p ∈ H, ∀ q ∈ H, ∀ v w g g', dec p (v, g) → dec q (w, g') → Cons v g w g'

/-- **Gradecast with a binary grade**: an honest output with grade `true` fixes the value of
every honest output. -/
abbrev BinaryGradecast (snd : P) : LockStep.Spec P V (V × Bool) :=
  Gradecast true (fun v g w _ => g = true → v = w) snd

/-- Binary gradecast in its usual form. -/
theorem binaryGradecast_iff {snd : P} {x : P → V} {H : Set P} {dec : P → V × Bool → Prop} :
    BinaryGradecast snd x H dec ↔ Termination H dec ∧ (snd ∈ H → ∀ p ∈ H, dec p (x snd, true)) ∧
      ∀ p ∈ H, ∀ q ∈ H, ∀ v w g, dec p (v, true) → dec q (w, g) → v = w := by
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h p hp q hq v w g hv hw =>
    h p hp q hq v w true g hv hw rfl, fun h p hp q hq v w g g' hv hw hg => ?_⟩
  subst hg
  exact h p hp q hq v w g' hv hw

/-! ### Output functions -/

section Functions

/-- **Consensus** (Byzantine agreement) on output functions: the honest outputs agree, and if all
honest inputs are `v`, every honest output is `v`. -/
structure Consensus (inp : P → V) (H : Set P) (out : P → V) : Prop where
  /-- Agreement: honest outputs coincide. -/
  agreement : ∀ i ∈ H, ∀ j ∈ H, out i = out j
  /-- Strong unanimity. -/
  unanimity : ∀ v, (∀ i ∈ H, inp i = v) → ∀ i ∈ H, out i = v

/-- **Graded consensus** (graded agreement) with a binary grade: every honest process outputs a
value and a grade `(out i).2 : Bool`.
* Validity (strong unanimity): if all honest inputs are `v`, every honest process outputs `v`
  with grade `true`.
* Coherence (graded agreement): if an honest process outputs grade `true`, every honest process
  outputs its value. -/
structure GradedConsensus (inp : P → V) (H : Set P) (out : P → V × Bool) : Prop where
  /-- Validity: unanimous honest inputs are output with grade `true`. -/
  validity : ∀ v, (∀ i ∈ H, inp i = v) → ∀ i ∈ H, (out i).1 = v ∧ (out i).2 = true
  /-- Coherence: a grade-`true` honest output fixes the value of every honest output. -/
  coherence : ∀ i ∈ H, (out i).2 = true → ∀ j ∈ H, (out j).1 = (out i).1

variable {inp : P → V} {H : Set P} {out : P → V × Bool}

/-- The two clauses of graded consensus as a conjunction. -/
theorem gradedConsensus_iff : GradedConsensus inp H out ↔
    (∀ v, (∀ i ∈ H, inp i = v) → ∀ i ∈ H, (out i).1 = v ∧ (out i).2 = true) ∧
      ∀ i ∈ H, (out i).2 = true → ∀ j ∈ H, (out j).1 = (out i).1 :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

end Functions

/-! ### Proxcensus -/

namespace Proxcensus

/-- The maximal grade `⌊(s - 1)/2⌋` of `s`-slot Proxcensus. -/
def maxGrade (s : ℕ) : ℕ := (s - 1) / 2

/-- Consistency of two outputs `a = (yᵢ, gᵢ)`, `b = (yⱼ, gⱼ)` of `s`-slot Proxcensus: the grades
differ by at most one, two positive grades carry the same value, and, for even `s`, a positive
grade `gᵢ` fixes the value `yⱼ`. -/
def Consistent (s : ℕ) (a b : V × ℕ) : Prop :=
  a.2 ≤ b.2 + 1 ∧ b.2 ≤ a.2 + 1 ∧ (1 ≤ a.2 → 1 ≤ b.2 → a.1 = b.1) ∧
    (s % 2 = 0 → 0 < a.2 → a.1 = b.1)

instance [DecidableEq V] (s : ℕ) (a b : V × ℕ) : Decidable (Consistent s a b) := by
  unfold Consistent; infer_instance

end Proxcensus

open Proxcensus in
/-- **`s`-slot Proxcensus** (Fitzi, Liu-Zhang, Loss, PODC 2021): every honest process outputs a
value and a grade in `[0, maxGrade s]`; unanimous honest inputs `v` give output `(v, maxGrade s)`;
and any two honest outputs are `Consistent s`. Odd `s` has a middle slot `(⊥, 0)` (the value of a
grade-`0` output is meaningless), even `s` does not: binary graded consensus (`GradedConsensus`)
is `4`-slot Proxcensus with grade `true` read as `1`. -/
structure Proxcensus (s : ℕ) (inp : P → V) (H : Set P) (out : P → V × ℕ) : Prop where
  /-- Grades are at most `maxGrade s`. -/
  grade_le : ∀ p ∈ H, (out p).2 ≤ maxGrade s
  /-- Validity: unanimous honest inputs are output with the maximal grade. -/
  validity : ∀ v, (∀ p ∈ H, inp p = v) → ∀ p ∈ H, out p = (v, maxGrade s)
  /-- Consistency of any two honest outputs. -/
  consistency : ∀ p ∈ H, ∀ q ∈ H, Consistent s (out p) (out q)

/-! ### Broadcast and interactive consistency -/

section Relations

variable (inp : P → V) (H : Set P)

/-- **Sender validity** (validity of Byzantine broadcast with sender `s`): if `s` is honest, every
honest process decides the input of `s`. -/
def SenderValidity (s : P) (dec : P → V → Prop) : Prop := s ∈ H → ∀ p ∈ H, dec p (inp s)

/-- **Vector validity** (validity of interactive consistency): in every decision vector of an
honest process, the entry of each honest process is its input. -/
def VectorValidity (dec : P → (P → V) → Prop) : Prop :=
  ∀ p ∈ H, ∀ d, dec p d → ∀ q ∈ H, d q = inp q

/-- **Input validity** (honest-input validity): every decision of an honest process is the input of
some honest process. -/
def InputValidity (dec : P → V → Prop) : Prop := ∀ p ∈ H, ∀ v, dec p v → ∃ q ∈ H, inp q = v

/-- CSLib's lock-step Byzantine broadcast is termination, sender validity and agreement. -/
theorem bb_iff (s : P) (dec : P → V → Prop) :
    LockStep.BB s inp H dec ↔ Termination H dec ∧ SenderValidity inp H s dec ∧ Agreement H dec :=
  Iff.rfl

/-- CSLib's lock-step interactive consistency is termination, vector validity and agreement. -/
theorem ic_iff (dec : P → (P → V) → Prop) :
    LockStep.IC inp H dec ↔ Termination H dec ∧ VectorValidity inp H dec ∧ Agreement H dec :=
  Iff.rfl

/-- CSLib's lock-step weak agreement is agreement on the non-`⊥` outputs. -/
theorem weakAgreement_iff (x : P → I) (dec : P → Option V → Prop) :
    LockStep.WeakAgreement x H dec ↔ Agreement H fun p v => dec p (some v) :=
  Iff.rfl

end Relations

/-! ### Approximate agreement -/

section Range

variable {inp : P → V} {H H' : Set P} {v w x : V}

/-- `v` lies in the **range of the honest inputs**: `inp p ≤ v ≤ inp q` for some honest `p` and
`q` (for real inputs: `v` lies in the interval `[min, max]` of the honest inputs). -/
def InRange [LE V] (inp : P → V) (H : Set P) (v : V) : Prop :=
  (∃ p ∈ H, inp p ≤ v) ∧ ∃ q ∈ H, v ≤ inp q

/-- `InRange` with both witnesses up front. -/
theorem inRange_iff_exists [LE V] :
    InRange inp H v ↔ ∃ p ∈ H, ∃ q ∈ H, inp p ≤ v ∧ v ≤ inp q :=
  ⟨fun ⟨⟨p, hp, h₁⟩, q, hq, h₂⟩ => ⟨p, hp, q, hq, h₁, h₂⟩,
    fun ⟨p, hp, q, hq, h₁, h₂⟩ => ⟨⟨p, hp, h₁⟩, q, hq, h₂⟩⟩

/-- An honest input lies in the honest range. -/
theorem InRange.self [Preorder V] {p : P} (hp : p ∈ H) : InRange inp H (inp p) :=
  ⟨⟨p, hp, le_rfl⟩, p, hp, le_rfl⟩

/-- The honest range is convex: a value between two values of the range is in the range. -/
theorem InRange.of_le_of_le [Preorder V] (hv : InRange inp H v) (hw : InRange inp H w) {u : V}
    (h₁ : v ≤ u) (h₂ : u ≤ w) : InRange inp H u :=
  ⟨hv.1.imp fun _ ⟨hp, h⟩ => ⟨hp, h.trans h₁⟩, hw.2.imp fun _ ⟨hq, h⟩ => ⟨hq, h₂.trans h⟩⟩

/-- The range grows with the set of processes. -/
theorem InRange.mono [LE V] (h : InRange inp H v) (hH : H ⊆ H') : InRange inp H' v :=
  ⟨h.1.imp fun _ ⟨hp, h⟩ => ⟨hH hp, h⟩, h.2.imp fun _ ⟨hq, h⟩ => ⟨hH hq, h⟩⟩

/-- If all honest inputs are `x`, the only value in the honest range is `x`. -/
theorem InRange.eq_of_forall_eq [PartialOrder V] (h : InRange inp H v)
    (hx : ∀ p ∈ H, inp p = x) : v = x := by
  obtain ⟨⟨p, hp, h₁⟩, q, hq, h₂⟩ := h
  rw [hx p hp] at h₁
  rw [hx q hq] at h₂
  exact le_antisymm h₂ h₁

/-- For finitely many honest processes, `v` lies in the honest range iff it lies in every interval
containing all honest inputs (i.e. in `[min, max]` of the honest inputs). -/
theorem inRange_iff_forall_mem_Icc [LinearOrder V] (hH : H.Finite) (hne : H.Nonempty) :
    InRange inp H v ↔ ∀ lo hi, (∀ p ∈ H, inp p ∈ Set.Icc lo hi) → v ∈ Set.Icc lo hi := by
  refine ⟨fun ⟨⟨p, hp, h₁⟩, q, hq, h₂⟩ lo hi h => ⟨(h p hp).1.trans h₁, h₂.trans (h q hq).2⟩,
    fun h => ?_⟩
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image H inp hH hne
  obtain ⟨q, hq, hmax⟩ := Set.exists_max_image H inp hH hne
  obtain ⟨h₁, h₂⟩ := h (inp p) (inp q) fun r hr => ⟨hmin r hr, hmax r hr⟩
  exact ⟨⟨p, hp, h₁⟩, q, hq, h₂⟩

end Range

section Approx

/-- **Range validity** (validity of approximate agreement): every decision of an honest process
lies in the range of the honest inputs. -/
def RangeValidity [LE V] (inp : P → V) (H : Set P) (dec : P → V → Prop) : Prop :=
  ∀ p ∈ H, ∀ v, dec p v → InRange inp H v

/-- **`ε`-agreement**: any two decisions of honest processes are at distance at most `ε`. -/
def EpsAgreement [Lattice V] [AddGroup V] (ε : V) (H : Set P) (dec : P → V → Prop) : Prop :=
  ∀ p ∈ H, ∀ q ∈ H, ∀ v w, dec p v → dec q w → |v - w| ≤ ε

/-- **`ε`-approximate agreement**: every honest process decides (termination), every honest
decision lies in the range of the honest inputs (validity), and any two honest decisions are at
distance at most `ε` (`ε`-agreement). -/
def ApproxAgreement [Lattice V] [AddGroup V] (ε : V) : LockStep.Spec P V V := fun inp H dec =>
  Termination H dec ∧ RangeValidity inp H dec ∧ EpsAgreement ε H dec

variable {inp : P → V} {H : Set P} {dec : P → V → Prop}

/-- `ε`-agreement is monotone in `ε`. -/
theorem EpsAgreement.mono [Lattice V] [AddGroup V] {ε ε' : V} (h : EpsAgreement ε H dec)
    (hε : ε ≤ ε') : EpsAgreement ε' H dec :=
  fun p hp q hq v w hv hw => (h p hp q hq v w hv hw).trans hε

/-- Range validity with unanimous honest inputs `x`: every honest decision is `x`. -/
theorem RangeValidity.eq_of_forall_eq [PartialOrder V] {x : V} (h : RangeValidity inp H dec)
    (hx : ∀ p ∈ H, inp p = x) {p : P} (hp : p ∈ H) {v : V} (hv : dec p v) : v = x :=
  (h p hp v hv).eq_of_forall_eq hx

end Approx

end Cslib.Byzantine.Problem
