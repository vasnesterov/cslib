/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.LockStep.Agreement

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

Output functions:
* `Consensus inp H out`: agreement and strong unanimity.
* `GradedConsensus inp H out`: graded consensus (graded agreement) with a binary grade.
* `Proxcensus s inp H out`: `s`-slot Proxcensus (grades `0, …, ⌊(s - 1)/2⌋`).

## Main statements

* `ba_iff`: CSLib's `LockStep.BA` is termination, strong unanimity and agreement.
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

end Cslib.Byzantine.Problem
