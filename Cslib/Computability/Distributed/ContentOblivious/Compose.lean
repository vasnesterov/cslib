/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.ContentOblivious.Prog

/-!
# Procedures and the composability condition

A *procedure* is a content-oblivious program whose nodes eventually *return* a result; a node that
has returned is terminated (it never reads, changes state or sends again in this procedure).
Procedures are run back-to-back: as soon as a node returns from one procedure it starts the next
one. Since pulses carry no content, a node still executing procedure `A` must never consume a pulse
that a neighbour already sent in the next procedure `B`.

`Proc.Composable` is the semantic condition that makes this safe (Chalopin, Chang, Di Luna, Zhou,
*Efficient Counting and Simulation in Content-Oblivious Rings*, PODC 2026, §4):
* `bounded`: every execution sends a bounded number of pulses (so every execution is finite);
* `final`: every final configuration is quiescent and every node has returned
  (quiescent termination);
* `clean`: whenever a node that has not returned is willing to read from a port whose neighbour
  has already returned, a pulse of the procedure is still in transit on that link — so in a
  composition the node reads a pulse of the current procedure, not of the next one.

The paper's "composable ending property" (Definition 8: a termination wave started by a unique
terminator that, afterwards, never waits on the wave's outgoing port) implies `clean`.
-/

@[expose] public section

namespace Cslib.ContentOblivious

/-- A procedure with inputs `I` and results `R`: a program whose terminated states are exactly the
states that carry a result. -/
structure Proc (I R : Type*) extends Prog I where
  /-- The returned value, once the node has returned. -/
  result : State → Option R
  /-- A node is terminated iff it has returned. -/
  terminated_eq : ∀ s, terminated s = (result s).isSome

namespace Proc

variable {I R : Type*} [Encodable I] [Inhabited I] {V : Type*} [DecidableEq V] [Fintype V]

/-- **Composability** of a procedure on wiring `W` with inputs `x` (see the module docstring). -/
structure Composable (P : Proc I R) (W : Wiring V) (x : V → I) : Prop where
  /-- Every execution sends a bounded number of pulses. -/
  bounded : ∃ B, ∀ c, P.Reach W x c → totalSent c ≤ B
  /-- Quiescent termination: final configurations are quiescent and every node has returned. -/
  final : ∀ c, P.Reach W x c → P.Final W c →
    P.Quiescent W c ∧ ∀ v, (P.result (c.st v)).isSome
  /-- A node that has not returned and waits on a port whose neighbour has returned has a pulse
  of the procedure in transit on that port. -/
  clean : ∀ c, P.Reach W x c → ∀ v j, P.result (c.st v) = none →
    P.ready (c.st v) j = true → (P.result (c.st (W.peer (v, j)).1)).isSome →
    c.recvd (v, j) < c.sent (W.peer (v, j))

/-- The results of `P` on `W` with inputs `x` are `r`: in every final configuration every node
`v` has returned `r v`. -/
def Returns (P : Proc I R) (W : Wiring V) (x : V → I) (r : V → R) : Prop :=
  ∀ c, P.Reach W x c → P.Final W c → ∀ v, P.result (c.st v) = some (r v)

end Proc

end Cslib.ContentOblivious
