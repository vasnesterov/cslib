/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.History

/-!
# Three definitions of linearizability

Sela, Herlihy and Petrank observed that the original definition of linearizability of Herlihy
and Wing contains a typo, which makes it neither local nor nonblocking, and proposed an amended
definition. We define:

* `LinearizableHW` — Definition 2.2 of Sela–Herlihy–Petrank = the original definition of
  Herlihy–Wing, *with the typo*: condition L2 is `<_H ⊆ <_S`.
* `Linearizable` — Definition 4.1 of Sela–Herlihy–Petrank (amended): L2 is
  `<_{complete(H')} ⊆ <_S`. This is the definition used by `Cslib.SharedMemory.IsLinearization`
  (see `Cslib.SharedMemory.HerlihyWing.cslib_linearizable_iff`).
* `LinearizableLP` — Definition 7.1 of Sela–Herlihy–Petrank (linearization points).

Operations of `H`, `H'`, `complete(H')` and `S` are identified by `OpId` (`(p, x, k)`: the
`k`-th operation of `p` on `x`); since `complete(H')` and `S` are equivalent (equal process
subhistories), this is exactly the identification used implicitly by Herlihy and Wing.

We also define list-based characterizations (`IsLinA`, `IsLinO`) that are convenient for
proofs: a linearization is a list `M` of operation records, i.e. the sequential history
`seqHist M`, whose operations get the identities `idsOf M`. Finally, `PendingInv`, `Total`,
`runOK` and `detSpec` (deterministic sequential specifications) are defined.

## References

* [M. P. Herlihy, J. M. Wing, *Linearizability: A Correctness Condition for Concurrent
  Objects*][HerlihyWing1990]
* [G. Sela, M. Herlihy, E. Petrank, *Brief Announcement: Linearizability: A
  Typo*][SelaHerlihyPetrank2021]
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

/-- **Definition 2.2** (original definition of linearizability, with the typo). A well-formed
history `H` is linearizable if it has an extension `H'` such that
L1: some legal sequential history `S` is equivalent to `complete(H')`, and
L2: `<_H ⊆ <_S`. -/
def LinearizableHW (spec : SeqSpec P X Op Res) (H : History P X Op Res) : Prop :=
  WellFormed H ∧ ∃ H', IsExtension H H' ∧ ∃ S, Legal spec S ∧ Equiv (complete H') S ∧
    ∀ a b, RT H a b → RT S a b

/-- **Definition 4.1** (amended linearizability). As Definition 2.2, but
L2: `<_{complete(H')} ⊆ <_S`. -/
def Linearizable (spec : SeqSpec P X Op Res) (H : History P X Op Res) : Prop :=
  WellFormed H ∧ ∃ H', IsExtension H H' ∧ ∃ S, Legal spec S ∧ Equiv (complete H') S ∧
    ∀ a b, RT (complete H') a b → RT S a b

/-- The records of `M` match `H`: the operation of `M` with identity `a` has the operation that
`a` invoked in `H`, and, if `a` completed in `H`, the response it got in `H`. -/
def Matches (H : History P X Op Res) (M : List (OpRec P X Op Res)) : Prop :=
  ∀ a e, (a, e) ∈ (idsOf M).zip M → opOf H a = some e.o ∧ (Completed H a → resOf H a = some e.r)

/-- **Definition 7.1** (linearizability by linearization points).

`M` is the resulting sequential history `S = seqHist M`: it contains every operation of `H`
(completed instance) and a subset `T` of the pending invocations (those pending instances that
occur in `M`), each with its operation and (for completed ones) its actual response; the
response of a pending invocation in `T` is the one recorded in `M`. The linearization point of
`a` is the gap `lp a` of `H` (after the first `lp a` events): after the invocation of `a`
(`Invoked (H.take (lp a)) a`) and, if `a` completed, not after its response. Several points may
lie in the same gap; their relative order is the order in `M` (this is how we model "distinct
points"). `S` is obtained by placing every operation at its point: `M` is ordered by the
points. -/
def LinearizableLP (spec : SeqSpec P X Op Res) (H : History P X Op Res) : Prop :=
  WellFormed H ∧ ∃ (M : List (OpRec P X Op Res)) (lp : OpId P X → ℕ),
    Matches H M ∧ (∀ a, Completed H a → a ∈ idsOf M) ∧
    (∀ a ∈ idsOf M, Invoked (H.take (lp a)) a ∧ (Completed H a → ¬ Completed (H.take (lp a)) a)) ∧
    (idsOf M).Pairwise (fun a b => lp a ≤ lp b) ∧ Legal spec (seqHist M)

/-- Common part of the list characterizations: the records match `H`, every operation of `H`
is linearized, the sequential history is legal, and the program order of every process is
respected. -/
structure LinCore (spec : SeqSpec P X Op Res) (H : History P X Op Res)
    (M : List (OpRec P X Op Res)) : Prop where
  recs : Matches H M
  complete : ∀ a, Completed H a → a ∈ idsOf M
  legal : Legal spec (seqHist M)
  procOrder : ∀ a b, a.p = b.p → Precedes H a b → b ∈ idsOf M → [a, b].Sublist (idsOf M)

/-- List characterization of the **amended** definition (Definition 4.1): real-time order is
respected towards every linearized operation, including linearized pending invocations. -/
structure IsLinA (spec : SeqSpec P X Op Res) (H : History P X Op Res)
    (M : List (OpRec P X Op Res)) : Prop extends LinCore spec H M where
  realtime : ∀ a b, Precedes H a b → b ∈ idsOf M → [a, b].Sublist (idsOf M)

/-- List characterization of the **original** definition (Definition 2.2): real-time order is
respected only among operations (completed instances) of `H`. -/
structure IsLinO (spec : SeqSpec P X Op Res) (H : History P X Op Res)
    (M : List (OpRec P X Op Res)) : Prop extends LinCore spec H M where
  realtime : ∀ a b, Precedes H a b → Completed H b → [a, b].Sublist (idsOf M)

/-- `H|p` ends with the pending invocation `inv p x o`. -/
def PendingInv (H : History P X Op Res) (p : P) (x : X) (o : Op) : Prop :=
  ∃ M, restrictP H p = seqHist M ++ [.inv p x o]

/-- An operation `o` of process `p` on object `x` is *total*: it is defined in every state,
i.e. it can be appended (with some response) to every legal complete sequential history of `x`.
-/
def Total (spec : SeqSpec P X Op Res) (p : P) (x : X) (o : Op) : Prop :=
  ∀ M : List (OpRec P X Op Res), (∀ e ∈ M, e.x = x) → seqHist M ∈ spec x →
    ∃ r, seqHist (M ++ [⟨p, x, o, r⟩]) ∈ spec x

/-- The sequential specification of a deterministic object, given by an initial state and a
transition function: the complete sequential histories whose responses are the ones the
transition function prescribes. -/
def runOK {State : Type} (δ : State → Op → State × Res) : State → List (OpRec P X Op Res) → Prop
  | _, [] => True
  | q, e :: M => (δ q e.o).2 = e.r ∧ runOK δ (δ q e.o).1 M

/-- The sequential specification of a deterministic object. -/
def detSpec {State : Type} (init : State) (δ : State → Op → State × Res) :
    Set (History P X Op Res) :=
  {s | ∃ M, s = seqHist M ∧ runOK δ init M}

end Cslib.SharedMemory.HerlihyWing
