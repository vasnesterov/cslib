/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.MessagePassing.Compose

/-! # Protocols with private inputs

In many problems every process starts with a *private input*: its proposal in consensus or
Byzantine agreement, a default value, and so on. An `InputProtocol P I X` is a protocol whose
processes receive a private input of type `X`: the initial state and the step function of process
`p` may depend on `p` and on its own input `v : X`, and on nothing else. Given an assignment
`x : P → X` of inputs, `InputProtocol.toProtocol x` is the ordinary protocol in which process `p`
gets the input `x p`.

## Why private inputs matter

It is tempting to model private inputs as a family of protocols `A : (P → X) → Protocol P I`
indexed by all inputs, with the informal convention that process `p` only uses `x p`. Nothing
enforces this convention, and problem specifications quantified over such families can become
trivial. For example, for Byzantine agreement with `3t < n`, the zero-message family in which every
process, when started, decides `f prop` for a *global* function `f` of all proposals (the value
proposed by at least `n - t` processes if there is one, and some valid proposal otherwise)
satisfies agreement, strong validity and external validity with latency `0`: every process decides
the same value `f prop` without communicating. With an `InputProtocol`, process `p` cannot read
the other processes' inputs, so such an "oracle" protocol cannot be expressed, and learning the
other inputs requires communication, as intended.

## Main definitions

* `InputProtocol P I X`: protocols for processes `P` implementing interface `I`, whose processes
  receive private inputs of type `X`.
* `InputProtocol.toProtocol A x`: the protocol in which process `p` gets the input `x p`.
* `InputProtocol.ofProtocol X A`: an ordinary protocol, ignoring its input.
* `InputProtocol.compose L C`: composition of a logic with children, all of which receive the
  private input of the process (see `Cslib.Distributed.Protocol.compose`).

## Main statements

* `InputProtocol.toProtocol_ofProtocol`, `InputProtocol.toProtocol_compose`: `toProtocol`
  commutes with the lift of ordinary protocols and with composition (both by `rfl`). Hence
  statements about runs of composite protocols apply verbatim to `(L.compose C).toProtocol x`.

## Implementation notes

A concrete family `F : (P → X) → Protocol P I` whose types do not depend on the inputs and in
which process `p` uses its argument `x` only through `x p` can be turned into an `InputProtocol`
by evaluating it at constant input assignments: `init p v := (F fun _ => v).init p` and
`step p v := (F fun _ => v).step p`; then `toProtocol x` is `F x` by `rfl`. For a non-local
family (such as the oracle above) this changes the protocol: process `p` then believes that all
processes have its own input.
-/

@[expose] public section

namespace Cslib.Distributed

/-- A protocol for processes `P` implementing the interface `I`, in which every process receives
a private input of type `X` (for example, its proposal).

Process `p` with input `v` starts in state `init p v` and handles its inputs with `step p v`: the
behaviour of a process depends only on its identity and on its own private input. -/
structure InputProtocol (P : Type*) (I : Interface) (X : Type*) where
  /-- Messages exchanged between processes. -/
  Msg : Type
  /-- Timer tags. -/
  Timer : Type
  /-- Local states. -/
  State : Type
  /-- The initial state of each process, given its private input. -/
  init : P → X → State
  /-- The step function: process, private input, local clock reading, input, state ↦ new state
  and outputs. -/
  step : P → X → ℕ → Input P Msg Timer I.Req → State → State × List (Output P Msg Timer I.Ind)

namespace InputProtocol

variable {P : Type*} {I : Interface} {X : Type*}

/-- The protocol in which process `p` receives the private input `x p`.

The definition is reducible so that the message, timer and state types unfold to those of `A`. -/
abbrev toProtocol (A : InputProtocol P I X) (x : P → X) : Protocol P I where
  Msg := A.Msg
  Timer := A.Timer
  State := A.State
  init p := A.init p (x p)
  step p := A.step p (x p)

variable (X) in
/-- An ordinary protocol, viewed as a protocol with private inputs of type `X` that it ignores. -/
abbrev ofProtocol (A : Protocol P I) : InputProtocol P I X where
  Msg := A.Msg
  Timer := A.Timer
  State := A.State
  init p _ := A.init p
  step p _ := A.step p

/-- A protocol that ignores its inputs is the same for every assignment of inputs. -/
@[simp]
theorem toProtocol_ofProtocol (A : Protocol P I) (x : P → X) : (ofProtocol X A).toProtocol x = A :=
  rfl

variable {ι : Type} {J : ι → Interface} [DecidableEq ι]

/-- The composition of a logic `L` with children `C i` (see `Protocol.compose`), where the logic
and all children of process `p` receive the private input of `p`.

The step of process `p` with input `v` is the step of `p` in the composite of the ordinary
protocols in which every process has input `v`; only the components of `p` are used, so this is
the step of `p` in `(L.toProtocol x).compose fun i => (C i).toProtocol x` whenever `x p = v`
(`toProtocol_compose`). -/
abbrev compose (L : InputProtocol P (I.uses J) X) (C : (i : ι) → InputProtocol P (J i) X) :
    InputProtocol P I X where
  Msg := L.Msg ⊕ Σ i, (C i).Msg
  Timer := L.Timer ⊕ Σ i, (C i).Timer
  State := L.State × ((i : ι) → (C i).State)
  init p v := (L.init p v, fun i => (C i).init p v)
  step p v := ((L.toProtocol fun _ => v).compose fun i => (C i).toProtocol fun _ => v).step p

/- The two sides are definitionally equal: at process `p`, both steps only use the components
`L.step p (x p)` and `(C i).step p (x p)`. The elaborator does not see this with smart unfolding,
because the auxiliary `match` functions of `Protocol.compose` take the component protocols as
arguments, and these differ at processes other than `p`. -/
set_option smartUnfolding false in
/-- Assigning private inputs commutes with composition (definitionally). -/
theorem toProtocol_compose (L : InputProtocol P (I.uses J) X)
    (C : (i : ι) → InputProtocol P (J i) X) (x : P → X) :
    (L.compose C).toProtocol x = (L.toProtocol x).compose fun i => (C i).toProtocol x :=
  rfl

end InputProtocol

end Cslib.Distributed
