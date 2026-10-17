/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Set.Defs

/-!
# The king phase of phase-king protocols

A phase of a phase-king protocol (Berman, Garay, Perry) runs a graded-consensus step, after which
every honest process holds a value `val i` and is either *strong* (high grade) or not, and then a
king step: a strong process keeps its value, a weak one adopts the value sent by the king `k`.
Two facts make phase king work, and only they depend on the king step:

* **agreement** (`kingPhase_agreement`): if the king is honest, all honest processes end the
  phase with the king's value, because a strong honest process holds the same value as every
  honest process (coherence of graded consensus), in particular as the king;
* **persistence** (`kingPhase_persistence`): if all honest processes are strong with value `v`
  (validity of graded consensus on unanimous inputs), they all keep `v`.

The statements allow a post-processing of the kept and adopted values (`keep`, `adopt`), as in
protocols that increment a counter in the king step. For a phase whose first part is a binary
graded consensus `gc` (`Cslib.Byzantine.Problem.GradedConsensus`), take `val i = (gc i).1` and
`strong i = ((gc i).2 = true)`: coherence gives the hypothesis of `kingPhase_agreement`, validity
that of `kingPhase_persistence`.

Instances: Lemma 4 of Lenzen–Rybicki–Suomela (PODC 2015, `lemma4`), Lemma 2.6 of
Lenzen–Sheikholeslami (PODC 2022, `lemma_2_6`), Lemma 2.7 of Lenzen–Loss (PODC 2026, `kc_spec`),
Lemma 11 of Khanchandani–Wattenhofer (PODC 2020, `good_phase`).
-/

@[expose] public section

namespace Cslib.Byzantine

variable {P α β : Type*} {H : Set P} {val : P → α} {strong : P → Prop} {out : P → β}
  {keep adopt : α → β} {k : P}

/-- **King phase, agreement.** Let the honest king `k` hold `val k`, and let every strong honest
process hold the king's value (by coherence of graded consensus a strong honest process holds the
value of every honest process). If strong honest processes output `keep (val i)`, weak ones output
`adopt (val k)`, and `adopt` and `keep` agree on the values of strong processes, then every honest
process outputs `adopt (val k)`. -/
theorem kingPhase_agreement (hcoh : ∀ i ∈ H, strong i → val k = val i)
    (hstrong : ∀ i ∈ H, strong i → out i = keep (val i))
    (hweak : ∀ i ∈ H, ¬ strong i → out i = adopt (val k))
    (hkeep : ∀ i ∈ H, strong i → adopt (val i) = keep (val i)) :
    ∀ i ∈ H, out i = adopt (val k) := by
  intro i hi
  by_cases hs : strong i
  · rw [hstrong i hi hs, hcoh i hi hs, hkeep i hi hs]
  · exact hweak i hi hs

/-- **King phase, persistence.** If every honest process is strong with value `v`, every honest
process outputs `keep v`, whatever the king sends. -/
theorem kingPhase_persistence {v : α} (hval : ∀ i ∈ H, strong i ∧ val i = v)
    (hstrong : ∀ i ∈ H, strong i → out i = keep (val i)) : ∀ i ∈ H, out i = keep v :=
  fun i hi => by rw [hstrong i hi (hval i hi).1, (hval i hi).2]

end Cslib.Byzantine
