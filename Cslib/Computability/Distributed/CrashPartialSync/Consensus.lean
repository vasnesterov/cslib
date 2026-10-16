/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.CrashPartialSync.Model

/-!
# Consensus in the crash-prone partially synchronous model

Specifications of consensus as a *task* (every process gets its input at time `0`;
`SolvesTask`) and as a shared *object* (processes call `propose(v)` at arbitrary times, at most
once each; `SolvesObject`: agreement, validity w.r.t. earlier invocations, wait-freedom), as in
Ryabinin, Gotsman and Sutra [RyabininGotsmanSutra2025] (§2 and §A).

## References

* [F. Ryabinin, A. Gotsman, P. Sutra, *Revisiting lower bounds for two-step
  consensus*][RyabininGotsmanSutra2025]
-/

@[expose] public section

namespace Cslib.CrashPartialSync

variable {P V M S : Type*} [Fintype P]

/-! ### Consensus specifications -/

/-- Invocations of a consensus *task* with initial configuration `I`: every process gets its
input at time `0`. -/
def taskInv (I : P → V) : P → ℕ → Option V := fun p τ => if τ = 0 then some (I p) else none

/-- An `f`-resilient implementation of the consensus **task** ([RyabininGotsmanSutra2025], §2,
Definition 1): in every valid run with at most `f` crashes, Validity (every decision is the input of
some process), Agreement (no two decisions differ, including decisions of processes that crash
later) and Termination (every correct process eventually decides). -/
structure SolvesTask (A : Protocol P V M S) (f : ℕ) : Prop where
  validity : ∀ (R : Run P V M) (I : P → V), R.Valid f → R.inv = taskInv I →
    ∀ p τ v, R.DecidesAt A p τ v → ∃ q, I q = v
  agreement : ∀ (R : Run P V M) (I : P → V), R.Valid f → R.inv = taskInv I →
    ∀ p q τ τ' v w, R.DecidesAt A p τ v → R.DecidesAt A q τ' w → v = w
  termination : ∀ (R : Run P V M) (I : P → V), R.Valid f → R.inv = taskInv I →
    ∀ p, R.crash p = none → ∃ τ v, R.DecidesAt A p τ v

/-- An `f`-resilient implementation of the consensus **object** (§2): in every valid run in which
every process calls `propose` at most once, responses agree, every response was proposed before
it was returned (together: linearizability w.r.t. the sequential consensus object), and every
call by a correct process returns (wait-freedom). -/
structure SolvesObject (A : Protocol P V M S) (f : ℕ) : Prop where
  validity : ∀ (R : Run P V M), R.Valid f → R.WellFormed →
    ∀ p τ v, R.RespondsAt A p τ v → ∃ q, ∃ τ₁ < τ, R.inv q τ₁ = some v
  agreement : ∀ (R : Run P V M), R.Valid f → R.WellFormed →
    ∀ p q τ τ' v w, R.RespondsAt A p τ v → R.RespondsAt A q τ' w → v = w
  waitFree : ∀ (R : Run P V M), R.Valid f → R.WellFormed →
    ∀ p τ₀ v, R.crash p = none → R.inv p τ₀ = some v → ∃ τ w, R.RespondsAt A p τ w

end Cslib.CrashPartialSync
