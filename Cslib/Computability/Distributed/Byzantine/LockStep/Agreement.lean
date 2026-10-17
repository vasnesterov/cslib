/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.LockStep.Auth

/-!
# Standard agreement specifications in the synchronous model

Specifications (`Spec P I O`) of Byzantine broadcast, Byzantine agreement and interactive
consistency, plus a notion of solving a problem "with omissions" (honest messages may be lost) and
of bounded termination.
-/

@[expose] public section

namespace Cslib.Byzantine.LockStep

variable {P V : Type*}

/-- **Byzantine broadcast** with sender `s` (termination, validity, consistency).
Only the input of `s` matters. -/
def BB (s : P) : Spec P V V := fun x H dec =>
  (∀ p ∈ H, ∃ v, dec p v) ∧
  (s ∈ H → ∀ p ∈ H, dec p (x s)) ∧
  (∀ p ∈ H, ∀ q ∈ H, ∀ v w, dec p v → dec q w → v = w)

/-- **Byzantine agreement** (termination, validity, agreement). -/
def BA : Spec P V V := fun x H dec =>
  (∀ p ∈ H, ∃ v, dec p v) ∧
  (∀ v, (∀ p ∈ H, x p = v) → ∀ p ∈ H, dec p v) ∧
  (∀ p ∈ H, ∀ q ∈ H, ∀ v w, dec p v → dec q w → v = w)

/-- **Interactive consistency**: honest parties agree on a vector whose honest entries are the
honest inputs. -/
def IC : Spec P V (P → V) := fun x H dec =>
  (∀ p ∈ H, ∃ d, dec p d) ∧
  (∀ p ∈ H, ∀ d, dec p d → ∀ q ∈ H, d q = x q) ∧
  (∀ p ∈ H, ∀ q ∈ H, ∀ d e, dec p d → dec q e → d = e)

/-- **Weak agreement** (for outputs with a failure value `none = ⊥`): two honest non-`⊥` outputs
coincide. -/
def WeakAgreement {I : Type*} : Spec P I (Option V) := fun _ H dec =>
  ∀ p ∈ H, ∀ q ∈ H, ∀ v w, dec p (some v) → dec q (some w) → v = w

/-- A spec on `Option`-valued outputs which holds on the `some` part: `spec` holds for the decision
relation `fun p v => dec p (some v)` and no honest party outputs `none`. -/
def SomeSpec {I : Type*} (spec : Spec P I V) : Spec P I (Option V) := fun x H dec =>
  (∀ p ∈ H, ¬ dec p none) ∧ spec x H (fun p v => dec p (some v))

variable {I M O : Type*}

/-- All honest parties have decided within `T` rounds. -/
def TerminatesBy (G : SimpleGraph P) (alg : Protocol P I M O) (s : Scenario P I M) (T : ℕ) : Prop :=
  ∀ p, p ∉ s.byz → ∃ r ≤ T, ∃ o, status G alg s r p = some o

/-- `alg` solves `spec` on reliable runs and `specOm` on all runs (honest messages may be omitted
arbitrarily), and terminates within `T` rounds in all runs. Unauthenticated adversary. -/
def SolvesWithOmissions (G : SimpleGraph P) (alg : Protocol P I M O) (Z : AdvStructure P)
    (spec specOm : Spec P I O) (T : ℕ) : Prop :=
  ∀ s : Scenario P I M, s.byz ∈ Z →
    (s.Reliable → spec s.input s.honest (Decides G alg s)) ∧
    specOm s.input s.honest (Decides G alg s) ∧ TerminatesBy G alg s T

end Cslib.Byzantine.LockStep
