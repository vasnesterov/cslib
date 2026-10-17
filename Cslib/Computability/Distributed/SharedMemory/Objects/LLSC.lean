/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Spec
public import Mathlib.Data.Finset.Insert

/-!
# Load-linked / store-conditional objects

Since the behaviour of `LL`, `VL`, `SC` and `RL` depends on the invoking process, these
operations carry the caller (its *link*) as an argument (an `ObjSpec` has no notion of the
invoking process); an implementation must pass its own identifier, which can be enforced with
`Impl.allowed`.

* `llscObj V K v₀` — an LL/SC object with values `V` and link owners `K` (`LL` / `SC` / `VL`).
  The state is the value together with the list of owners of valid links; every response is
  the current value together with a success bit.
* `rllsc P V v₀` — the context-aware *releasable* LL/SC object (R-LLSC) of Attiya, Bender,
  Farach-Colton, Oshman and Schiller (PODC 2024), with additional operations `RL` (release the
  link), `Load` and `Store`. The state is the value together with the set of processes holding
  a valid link (the *context*); responses are `V ⊕ Bool` (`inl val` for `LL` and `Load`).
-/

@[expose] public section

namespace Cslib.SharedMemory

/-! ## LL/SC -/

/-- Operations of an LL/SC object; the argument `k` is the calling process (its link). -/
inductive LLOp (V K : Type) where
  /-- `LL()`: create a link, return the value. -/
  | ll (k : K)
  /-- `SC(v)`: if the caller's link is valid, write `v` and invalidate all links. -/
  | sc (k : K) (v : V)
  /-- `VL()`: report whether the caller's link is valid. -/
  | vl (k : K)

/-- An LL/SC object with values `V` and link owners `K`. The state is the value together
with the list of owners of valid links. `LL` returns the value and creates a link; `SC(v)`
succeeds iff the caller has a valid link, in which case it writes `v` and invalidates all
links; `VL` reports whether the caller's link is valid. The response is the current value
together with a success bit. -/
abbrev llscObj (V K : Type) [DecidableEq K] (v₀ : V) : ObjSpec where
  State := V × List K
  Op := LLOp V K
  Resp := V × Bool
  init := (v₀, [])
  δ s
    | .ll k => ((s.1, if k ∈ s.2 then s.2 else k :: s.2), (s.1, true))
    | .sc k v => if k ∈ s.2 then ((v, []), (s.1, true)) else (s, (s.1, false))
    | .vl k => (s, (s.1, decide (k ∈ s.2)))

namespace llscObj

variable {V K : Type} [DecidableEq K] {v₀ : V} (s : V × List K) (k : K)

@[simp] lemma δ_ll :
    (llscObj V K v₀).δ s (.ll k) = ((s.1, if k ∈ s.2 then s.2 else k :: s.2), (s.1, true)) :=
  rfl

@[simp] lemma δ_sc (v : V) : (llscObj V K v₀).δ s (.sc k v) =
    if k ∈ s.2 then ((v, []), (s.1, true)) else (s, (s.1, false)) := rfl

@[simp] lemma δ_vl : (llscObj V K v₀).δ s (.vl k) = (s, (s.1, decide (k ∈ s.2))) := rfl

end llscObj

/-! ## Releasable LL/SC (R-LLSC) -/

/-- Operations of an R-LLSC object over values `V`, for processes `P`. -/
inductive RLLSCOp (P V : Type) where
  | ll (p : P)
  | vl (p : P)
  | sc (p : P) (v : V)
  | rl (p : P)
  | load
  | store (v : V)

/-- The process an operation must be invoked by (`none` for `Load`/`Store`, which any process
may invoke). -/
def RLLSCOp.proc {P V : Type} : RLLSCOp P V → Option P
  | .ll p | .vl p | .sc p _ | .rl p => some p
  | .load | .store _ => none

/-- The R-LLSC object over `V` with initial value `v₀` (context initially empty). -/
@[reducible] def rllsc (P V : Type) [DecidableEq P] (v₀ : V) : ObjSpec where
  State := V × Finset P
  Op := RLLSCOp P V
  Resp := V ⊕ Bool
  init := (v₀, ∅)
  δ s
    | .ll p => ((s.1, insert p s.2), .inl s.1)
    | .vl p => (s, .inr (decide (p ∈ s.2)))
    | .sc p v => if p ∈ s.2 then ((v, ∅), .inr true) else (s, .inr false)
    | .rl p => ((s.1, s.2.erase p), .inr true)
    | .load => (s, .inl s.1)
    | .store v => ((v, ∅), .inr true)

namespace rllsc

variable {P V : Type} [DecidableEq P] {v₀ : V} (s : V × Finset P) (p : P) (v : V)

@[simp] lemma δ_ll : (rllsc P V v₀).δ s (.ll p) = ((s.1, insert p s.2), .inl s.1) := rfl
@[simp] lemma δ_vl : (rllsc P V v₀).δ s (.vl p) = (s, .inr (decide (p ∈ s.2))) := rfl
@[simp] lemma δ_sc : (rllsc P V v₀).δ s (.sc p v) =
    if p ∈ s.2 then ((v, ∅), .inr true) else (s, .inr false) := rfl
@[simp] lemma δ_rl : (rllsc P V v₀).δ s (.rl p) = ((s.1, s.2.erase p), .inr true) := rfl
@[simp] lemma δ_load : (rllsc P V v₀).δ s .load = (s, .inl s.1) := rfl
@[simp] lemma δ_store : (rllsc P V v₀).δ s (.store v) = ((v, ∅), .inr true) := rfl

end rllsc

end Cslib.SharedMemory
