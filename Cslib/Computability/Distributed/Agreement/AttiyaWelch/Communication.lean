/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Agreement.AttiyaWelch.Protocol
public import Cslib.Computability.Distributed.MessagePassing.Bits

/-! # The Attiya–Welch graded consensus protocol AW′: communication

Communication of AW′ (`Cslib.Distributed.AttiyaWelch.protocol`) in every run: a process sends at
most `K = ⌊n / (t + 1)⌋ + 6` messages to each process, hence at most `n · K` messages and, if
every value is encoded with at most `L` bits, at most `n · K · (L + 5)` bits. This is a property
of the local state machine; it does not depend on the validity of the run. If `n ≤ 3t + 2` (in
particular for `n = 3t + 1`, the setting of Attiya and Welch), then `⌊n / (t + 1)⌋ ≤ 2` and
`K ≤ 8`, so a process sends `O(n)` messages and `O(n L)` bits, in line with the `O(n² L)` total
bit complexity claimed for AW by [Civit et al.][CivitEtAl2024] (appendix, "Attiya-Welch Graded
Consensus Algorithm"). In general `K` grows with `n / (t + 1)` (e.g. `K = n + 6` for `t = 0`).

A process broadcasts its `INIT` once, `ECHO_1 a` at most once for each value `a` with which the
guard of phase `1` fires, and at most one `ECHO_k` for each phase `k = 2, …, 5`
(`card_sent_le`). The guard of phase `1` fires for `⊥` and for values `x` sent in `INIT` by more
than `t` processes; since only the first `INIT` of each sender is recorded
(`eq_of_mem_rcv_init`), there are at most `⌊n / (t + 1)⌋` such values (`card_sent_one_le`).

## Main definitions

* `AttiyaWelch.Msg.size`: the size in bits of a message, for given sizes of the values.

## Main statements

* `AttiyaWelch.card_sent_one_le`: the guard of phase `1` fires for at most `⌊n / (t + 1)⌋ + 1`
  values.
* `AttiyaWelch.countP_send_le`: a process sends at most `⌊n / (t + 1)⌋ + 6` messages to each
  process.
* `AttiyaWelch.bitsSent_one_le`: a process sends at most `n (⌊n / (t + 1)⌋ + 6)` messages.
* `AttiyaWelch.bitsSent_le`: a process sends at most `n (⌊n / (t + 1)⌋ + 6) (L + 5)` bits if the
  values are encoded with at most `L` bits.

## References

* [P. Civit, M. A. Dzulfikar, S. Gilbert, R. Guerraoui, J. Komatovic, M. Vidigueira,
  I. Zablotchi, *Partial Synchrony for Free? New Upper Bounds for Byzantine Agreement*,
  arXiv:2402.10059][CivitEtAl2024]
* [H. Attiya, J. L. Welch, *Multi-Valued Connected Consensus: A New Perspective on Crusader
  Agreement and Adopt-Commit*, OPODIS 2023][AttiyaWelch2023]
-/

@[expose] public section

namespace Cslib.Distributed

namespace AttiyaWelch

open GradedConsensus Finset

variable {P Value : Type}

/-! ### Message sizes -/

/-- The size in bits of a message of AW′ in a straightforward encoding, given the sizes
`valueSize` of the encodings of the values: one bit tells `INIT` from `ECHO`; `INIT x` continues
with the encoding of `x`; `ECHO_k a` continues with three bits for the phase `k`, one bit telling
`⊥` from a value, and the encoding of the value, if any. -/
def Msg.size (valueSize : Value → ℕ) : Msg Value → ℕ
  | .init x => 1 + valueSize x
  | .echo _ none => 1 + 3 + 1
  | .echo _ (some x) => 1 + 3 + 1 + valueSize x

/-- A message has at most `L + 5` bits if every value has at most `L` bits. -/
theorem Msg.size_le {valueSize : Value → ℕ} {L : ℕ} (hL : ∀ v, valueSize v ≤ L)
    (m : Msg Value) : m.size valueSize ≤ L + 5 := by
  rcases m with x | ⟨k, _ | x⟩
  · have := hL x; simp only [Msg.size]; omega
  · simp only [Msg.size]; omega
  · have := hL x; simp only [Msg.size]; omega

variable [DecidableEq P] [DecidableEq Value] [Fintype P] {t : ℕ}

/-! ### Messages of a process -/

section Local

variable {p : P} {s : State P Value}

/-- *Phase 1 messages*: the guard of phase `1` fires for at most `n / (t + 1)` values of `Value`
(each was sent in `INIT` by more than `t` processes, and at most one `INIT` is recorded from each
sender), and for `⊥`. -/
theorem card_sent_one_le (hs : (protocol P Value t).Reachable p s) :
    #(s.sent .one) ≤ Fintype.card P / (t + 1) + 1 := by
  let X : Finset Value := (s.sent .one).preimage some (Option.some_injective Value).injOn
  have hX : #X ≤ Fintype.card P / (t + 1) :=
    Quorum.card_le_div_of_pairwiseDisjoint (S := fun x => s.rcv (.init x))
      (fun x _ y _ hxy => Finset.disjoint_left.2 fun q hx hy => hxy (eq_of_mem_rcv_init hs hx hy))
      fun x hx => cand_of_mem_sent hs (Finset.mem_preimage.1 hx)
  have hsub : s.sent .one ⊆ insert none (X.map ⟨some, Option.some_injective _⟩) := by
    intro a ha
    cases a with
    | none => simp
    | some x => simp [X, ha]
  calc #(s.sent .one) ≤ #(insert none (X.map ⟨some, Option.some_injective _⟩)) :=
        card_le_card hsub
    _ ≤ #X + 1 := (card_insert_le _ _).trans (by rw [card_map])
    _ ≤ Fintype.card P / (t + 1) + 1 := by omega

/-- The number of messages that a process in state `s` has sent to each process: once it has
proposed, its `INIT` and one `ECHO_k a` for every value `a` with which the guard of phase `k`
has fired; nothing before. -/
def State.numSent (s : State P Value) : ℕ :=
  if s.proposed then 1 + (Phase.all.map fun k => #(s.sent k)).sum else 0

/-- A process sends at most `n / (t + 1) + 6` messages to each process: one `INIT`, at most
`n / (t + 1) + 1` `ECHO_1` (`card_sent_one_le`), and at most one `ECHO_k` for each phase
`k = 2, …, 5` (`card_sent_le`). -/
theorem numSent_le (hs : (protocol P Value t).Reachable p s) :
    s.numSent ≤ Fintype.card P / (t + 1) + 6 := by
  have h₁ := card_sent_one_le hs
  have h₂ := card_sent_le hs (k := .two) (by decide)
  have h₃ := card_sent_le hs (k := .three) (by decide)
  have h₄ := card_sent_le hs (k := .four) (by decide)
  have h₅ := card_sent_le hs (k := .five) (by decide)
  unfold State.numSent
  split_ifs
  · simp only [Phase.all, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · omega

omit [DecidableEq Value] in
/-- The `ECHO`s of a guard pass send one message to each process for every phase `k` and every
value in `nv k`. -/
theorem countP_dest_echoOuts (q : P) (nv : Phase → Finset (Option Value)) :
    (echoOuts nv : List (Output P (Msg Value) Empty (Ind Value))).countP
      (fun o => o.dest? = some q) = (Phase.all.map fun k => #(nv k)).sum := by
  simp only [echoOuts, List.countP_flatMap, Function.comp_def, countP_dest_broadcast,
    List.map_const', length_toList, List.sum_replicate, nsmul_eq_mul, mul_one]
  rfl

/-- A step sends at most as many messages to each process as it raises `State.numSent`. -/
theorem countP_dest_step_add_le (q : P) {x : Input P (Msg Value) Empty (Req Value)} :
    (step t p x s).2.countP (fun o => o.dest? = some q) + s.numSent ≤
      (step t p x s).1.numSent := by
  cases x with
  | req r =>
    cases r with
    | propose v =>
      cases hp : s.proposed <;> cases hab : s.ab <;>
        simp [step, hp, hab, State.numSent, countP_dest_echoOuts, countP_dest_broadcast]
    | abandon => exact (Nat.zero_add _).le
  | recv r m =>
    by_cases hab : s.ab
    · simp [step, hab, State.numSent]
    · have hk : ∀ k, #(s.sent k ∪ newVals t (record r m s.rcv) s.sent m k) =
          #(s.sent k) + #(newVals t (record r m s.rcv) s.sent m k) := fun k =>
        card_union_of_disjoint (disjoint_left.2 fun a ha hb => (cand_of_mem_newVals hb).2 ha)
      cases hp : s.proposed
      · simp [step, hab, hp, State.numSent]
      · simp [step, hab, hp, State.numSent, countP_dest_echoOuts, hk, List.sum_map_add,
          Function.comp_def]
        omega
  | timeout k => exact k.elim

end Local

/-! ### Communication in runs -/

/-- **Messages of AW′ to each process**: in every run, before any time `T`, a process sends at
most `n / (t + 1) + 6` messages to each process (`numSent_le`). This is a property of the local
state machine; it does not depend on the validity of the run. -/
theorem countP_send_le (ρ : Run (protocol P Value t)) (p q : P) (T : ℕ) :
    ((List.range T).flatMap (ρ.output p)).countP (fun o => o.dest? = some q) ≤
      Fintype.card P / (t + 1) + 6 := by
  have := Run.countP_output_add_le ρ (p := p) (c := fun o => o.dest? = some q)
    (f := State.numSent) (fun _ x s => countP_dest_step_add_le (t := t) q (x := x) (s := s)) T
  have h := numSent_le (ρ.reachable_state p T)
  have h₀ : State.numSent ((protocol P Value t).init p) = 0 := rfl
  omega

/-- **Messages of AW′**: in every run, in every window of time, a process sends at most
`n (n / (t + 1) + 6)` messages. -/
theorem bitsSent_one_le (ρ : Run (protocol P Value t)) (p : P) (a b : ℕ) :
    ρ.bitsSent (fun _ => 1) p a b ≤ Fintype.card P * (Fintype.card P / (t + 1) + 6) := by
  calc ρ.bitsSent (fun _ => 1) p a b ≤ ρ.bitsSent (fun _ => 1) p 0 b :=
        Run.bitsSent_mono (Nat.zero_le _) le_rfl
    _ = ∑ q, (((List.range' 0 (b - 0)).flatMap (ρ.output p)).filterMap
          (Output.msgTo? q)).length := Run.bitsSent_one
    _ ≤ ∑ _q : P, (Fintype.card P / (t + 1) + 6) := Finset.sum_le_sum fun q _ => by
        rw [length_filterMap_msgTo?, Nat.sub_zero, ← List.range_eq_range']
        exact countP_send_le ρ p q b
    _ = Fintype.card P * (Fintype.card P / (t + 1) + 6) := by
        rw [Finset.sum_const, Finset.card_univ]
        rfl

/-- **Bits of AW′**: in every run, in every window of time, a process sends at most
`n (n / (t + 1) + 6) (L + 5)` bits, if every value is encoded with at most `L` bits
(`Msg.size`). -/
theorem bitsSent_le (ρ : Run (protocol P Value t)) (p : P) (a b : ℕ) {valueSize : Value → ℕ}
    {L : ℕ} (hL : ∀ v, valueSize v ≤ L) :
    ρ.bitsSent (Msg.size valueSize) p a b ≤
      Fintype.card P * (Fintype.card P / (t + 1) + 6) * (L + 5) :=
  (Run.bitsSent_le_mul (Msg.size_le hL)).trans (Nat.mul_le_mul_right _ (bitsSent_one_le ρ p a b))

end AttiyaWelch

end Cslib.Distributed
