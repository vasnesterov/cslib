/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.MessagePassing.Compose
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Bits sent by the processes of a run

The *bit complexity* of a process is the number of bits it sends; for partially synchronous
algorithms, [Civit et al., *Partial synchrony for free?*][CivitEtAl2024] (§3) counts the bits that
a correct process sends during `[GST, ∞)`, since the number of bits sent before GST is unbounded
in the worst case. Message sizes are given by a function `size : Msg → ℕ` on the messages of the
protocol (the number of bits of the encoding of each message).

## Main definitions

* `Output.bits size o`: the bits sent by an output (the size of its message, `0` for indications
  and timers).
* `Run.bitsSent ρ size p a b`: the bits sent by process `p` at the times in `[a, b)`. With
  `size = fun _ => 1` it is the number of messages sent.
* `Compose.msgSize`: the sizes of the messages of a composite protocol, given those of the logic
  and of the children.

## Main statements

* `sum_map_bits_broadcast`: a broadcast of `m` sends `n · size m` bits.
* `Run.bitsSent_eq_sum_Ico`: the bits sent in a window are the sum of the bits sent at its times.
* `Run.bitsSent_add`, `Run.bitsSent_mono`, `Run.bitsSent_mono_size`: additivity over consecutive
  windows and monotonicity in the window and in the size function; `Run.bitsSent_add_size`,
  `Run.bitsSent_mul_size`: linearity in the size function; `Run.bitsSent_eq_zero`: a process that
  sends no message sends no bits.
* `Run.bitsSent_le_mul`: the bits are at most the number of messages times a bound on the sizes;
  `Run.bitsSent_one`: the number of messages is the sum over the receivers of the number of
  messages sent to each.
* `Run.bitsSent_add_le`: a potential on local states that grows by at least the bits sent at each
  step bounds the bits sent.
* `Run.exists_of_eq`: a run of a protocol is a run of every protocol equal to it, with the same
  history, validity and bits (for the message sizes transported along the equality).
* `Run.bitsSent_compose` (per time: `Run.sum_bits_output_compose`; finitely many children:
  `Run.bitsSent_compose_univ`): the bits sent by a process of a composite are the bits sent by its
  logic plus the bits sent by its children (if the message of a component is tagged, the tag is
  part of the size function of the component).

## References

* [P. Civit, M. A. Dzulfikar, S. Gilbert, R. Guerraoui, J. Komatovic, M. Vidigueira,
  I. Zablotchi, *Partial Synchrony for Free? New Upper Bounds for Byzantine Agreement*,
  arXiv:2402.10059][CivitEtAl2024]
-/

@[expose] public section

namespace Cslib.Distributed

variable {P : Type*}

/-! ### Bits of outputs -/

section Output

variable {Msg Timer Ind : Type*} (size : Msg → ℕ)

/-- The bits sent by an output, for the message sizes `size`: the size of the message it sends,
and `0` for indications and timers. -/
def Output.bits : Output P Msg Timer Ind → ℕ
  | .send _ m => size m
  | _ => 0

@[simp] theorem Output.bits_send (q : P) (m : Msg) :
    Output.bits size (.send q m : Output P Msg Timer Ind) = size m := rfl
@[simp] theorem Output.bits_ind (i : Ind) :
    Output.bits size (.ind i : Output P Msg Timer Ind) = 0 := rfl
@[simp] theorem Output.bits_setTimer (k : Timer) (T : ℕ) :
    Output.bits size (.setTimer k T : Output P Msg Timer Ind) = 0 := rfl

variable {size}

/-- The bits of a list of outputs depend monotonically on the message sizes. -/
theorem sum_map_bits_mono {size' : Msg → ℕ} (h : ∀ m, size m ≤ size' m)
    (l : List (Output P Msg Timer Ind)) :
    (l.map (Output.bits size)).sum ≤ (l.map (Output.bits size')).sum := by
  refine List.sum_le_sum fun o _ => ?_
  rcases o with ⟨q, m⟩ | i | ⟨k, T⟩ <;> simp [h]

/-- The bits of a list of outputs for the sum of two size functions. -/
theorem sum_map_bits_add (size' : Msg → ℕ) (l : List (Output P Msg Timer Ind)) :
    (l.map (Output.bits fun m => size m + size' m)).sum =
      (l.map (Output.bits size)).sum + (l.map (Output.bits size')).sum := by
  rw [← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun o _ => ?_
  rcases o with ⟨q, m⟩ | i | ⟨k, T⟩ <;> simp

/-- The bits of a list of outputs for a multiple of a size function. -/
theorem sum_map_bits_mul (c : ℕ) (l : List (Output P Msg Timer Ind)) :
    (l.map (Output.bits fun m => c * size m)).sum = c * (l.map (Output.bits size)).sum := by
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun o _ => ?_
  rcases o with ⟨q, m⟩ | i | ⟨k, T⟩ <;> simp

/-- The bits of a list of outputs are at most the number of messages it sends times a bound on
the sizes. -/
theorem sum_map_bits_le_mul {M : ℕ} (h : ∀ m, size m ≤ M) (l : List (Output P Msg Timer Ind)) :
    (l.map (Output.bits size)).sum ≤ (l.map (Output.bits fun _ => 1)).sum * M := by
  rw [Nat.mul_comm, ← sum_map_bits_mul]
  exact sum_map_bits_mono (fun m => by simpa using h m) l

/-- The bits of a list of outputs are the sum, over the receivers `q`, of the sizes of the
messages sent to `q`. -/
theorem sum_map_bits_eq_sum_msgTo? [Fintype P] [DecidableEq P] (size : Msg → ℕ)
    (l : List (Output P Msg Timer Ind)) :
    (l.map (Output.bits size)).sum = ∑ q, ((l.filterMap (Output.msgTo? q)).map size).sum := by
  induction l with
  | nil => simp
  | cons o l ih =>
    have h : ∀ q, (((o :: l).filterMap (Output.msgTo? q)).map size).sum =
        (if o.dest? = some q then o.bits size else 0) +
          ((l.filterMap (Output.msgTo? q)).map size).sum := by
      intro q
      rcases o with ⟨r, m⟩ | i | ⟨k, T⟩
      · by_cases h : r = q <;> simp [h]
      · simp [List.filterMap_cons]
      · simp [List.filterMap_cons]
    rw [List.map_cons, List.sum_cons, ih, Finset.sum_congr rfl fun q _ => h q,
      Finset.sum_add_distrib]
    congr 1
    rcases o with ⟨r, m⟩ | i | ⟨k, T⟩ <;> simp [Finset.sum_ite_eq]

/-- A broadcast of `m` sends `n · size m` bits. -/
theorem sum_map_bits_broadcast [Fintype P] (size : Msg → ℕ) (m : Msg) :
    ((Output.broadcast m : List (Output P Msg Timer Ind)).map (Output.bits size)).sum =
      Fintype.card P * size m := by
  simp only [Output.broadcast, List.map_map, Function.comp_def, Output.bits_send, List.map_const',
    List.sum_replicate, Finset.length_toList, Finset.card_univ]
  rfl

/-- Broadcasting one message per element of a finite set `S` sends `n · |S|` messages. -/
theorem sum_map_bits_one_flatMap_broadcast [Fintype P] {α : Type*} (S : Finset α)
    (f : α → Msg) :
    ((S.toList.flatMap fun a => (Output.broadcast (f a) : List (Output P Msg Timer Ind))).map
      (Output.bits fun _ => 1)).sum = Fintype.card P * S.card := by
  rw [← Finset.length_toList S]
  induction S.toList with
  | nil => simp
  | cons a l ih =>
    simp [List.flatMap_cons, sum_map_bits_broadcast, ih, Nat.mul_add, Nat.add_comm]

end Output

/-! ### Bits sent in a run -/

namespace Run

variable {I : Interface} {A : Protocol P I}

/-- The bits sent by process `p` at the times in `[a, b)` in the run `ρ`, for the message sizes
`size`: the sum of the sizes of the messages that `p` sends at these times. -/
def bitsSent (ρ : Run A) (size : A.Msg → ℕ) (p : P) (a b : ℕ) : ℕ :=
  (((List.range' a (b - a)).flatMap (ρ.output p)).map (Output.bits size)).sum

variable {size size' : A.Msg → ℕ} {ρ : Run A} {p : P} {a b c : ℕ}

/-- The bits sent in a window are the sum over its times of the bits sent at each time. -/
theorem bitsSent_eq_sum_Ico :
    ρ.bitsSent size p a b = ∑ τ ∈ Finset.Ico a b, ((ρ.output p τ).map (Output.bits size)).sum := by
  rw [bitsSent, Nat.Ico_eq_range', Finset.sum_eq_multiset_sum]
  simp only [Multiset.map_coe, Multiset.sum_coe]
  generalize List.range' a (b - a) = l
  induction l with
  | nil => rfl
  | cons τ l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem bitsSent_of_le (h : b ≤ a) : ρ.bitsSent size p a b = 0 := by
  simp [bitsSent, Nat.sub_eq_zero_of_le h]

@[simp]
theorem bitsSent_self : ρ.bitsSent size p a a = 0 :=
  bitsSent_of_le le_rfl

/-- The bits sent in consecutive windows add up. -/
theorem bitsSent_add (hab : a ≤ b) (hbc : b ≤ c) :
    ρ.bitsSent size p a b + ρ.bitsSent size p b c = ρ.bitsSent size p a c := by
  simp only [bitsSent_eq_sum_Ico]
  exact Finset.sum_Ico_consecutive _ hab hbc

/-- The bits sent in a window grow with the window. -/
theorem bitsSent_mono {a' b' : ℕ} (ha : a' ≤ a) (hb : b ≤ b') :
    ρ.bitsSent size p a b ≤ ρ.bitsSent size p a' b' := by
  simp only [bitsSent_eq_sum_Ico]
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico ha hb)

/-- The bits sent depend monotonically on the message sizes. -/
theorem bitsSent_mono_size (h : ∀ m, size m ≤ size' m) :
    ρ.bitsSent size p a b ≤ ρ.bitsSent size' p a b :=
  sum_map_bits_mono h _

/-- The bits sent for the sum of two size functions. -/
theorem bitsSent_add_size :
    ρ.bitsSent (fun m => size m + size' m) p a b = ρ.bitsSent size p a b + ρ.bitsSent size' p a b :=
  sum_map_bits_add _ _

/-- The bits sent for a multiple of a size function. -/
theorem bitsSent_mul_size (k : ℕ) :
    ρ.bitsSent (fun m => k * size m) p a b = k * ρ.bitsSent size p a b :=
  sum_map_bits_mul _ _

/-- The bits sent are at most the number of messages sent times a bound `M` on the message
sizes. -/
theorem bitsSent_le_mul {M : ℕ} (h : ∀ m, size m ≤ M) :
    ρ.bitsSent size p a b ≤ ρ.bitsSent (fun _ => 1) p a b * M :=
  sum_map_bits_le_mul h _

/-- The number of messages sent in a window is the sum, over the receivers `q`, of the number of
messages sent to `q`. -/
theorem bitsSent_one [Fintype P] [DecidableEq P] :
    ρ.bitsSent (fun _ => 1) p a b =
      ∑ q, (((List.range' a (b - a)).flatMap (ρ.output p)).filterMap (Output.msgTo? q)).length := by
  rw [bitsSent, sum_map_bits_eq_sum_msgTo?]
  simp only [List.map_const', List.sum_replicate]
  exact Finset.sum_congr rfl fun q _ => Nat.mul_one _

/-- A process that sends no message in a window sends no bits in it. -/
theorem bitsSent_eq_zero (h : ∀ τ, a ≤ τ → τ < b → ∀ q m, .send q m ∉ ρ.output p τ) :
    ρ.bitsSent size p a b = 0 := by
  rw [bitsSent_eq_sum_Ico]
  refine Finset.sum_eq_zero fun τ hτ => ?_
  rw [Finset.mem_Ico] at hτ
  refine List.sum_eq_zero fun n hn => ?_
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hn
  rcases o with ⟨q, m⟩ | i | ⟨k, T⟩
  · exact absurd ho (h τ hτ.1 hτ.2 q m)
  · rfl
  · rfl

/-- *Bits bounded by a potential.* If every step sends at most as many bits as it raises a
potential `f` on local states, then the bits sent in `[a, b)` are bounded by the growth of `f`
from time `a` to time `b`. -/
theorem bitsSent_add_le {f : A.State → ℕ}
    (hf : ∀ now x s, ((A.step p now x s).2.map (Output.bits size)).sum + f s ≤
      f (A.step p now x s).1) (hab : a ≤ b) :
    ρ.bitsSent size p a b + f (ρ.state p a) ≤ f (ρ.state p b) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hb : ρ.bitsSent size p b (b + 1) + f (ρ.state p b) ≤ f (ρ.state p (b + 1)) := by
      rw [bitsSent, Nat.add_sub_cancel_left, List.range'_one, List.flatMap_singleton, output,
        steps, state_succ]
      generalize ρ.state p b = s
      induction ρ.input p b generalizing s with
      | nil => simp
      | cons x xs ih' =>
        have h₁ := hf (ρ.clock p b) x s
        have h₂ := ih' (A.step p (ρ.clock p b) x s).1
        simp only [Protocol.batch_cons, List.flatMap_cons, List.map_append, List.sum_append]
          at h₂ ⊢
        omega
    rw [← bitsSent_add hab (Nat.le_add_right b 1)]
    omega

/-- **Runs along an equality of protocols.** If `A = A'`, every run of `A` is a run of `A'` with
the same faulty processes, GST, history and validity, which sends the same bits for the message
sizes transported along the equality. This transfers results about a protocol to a protocol that
is only propositionally equal to it (e.g. a composite assembled in a different way). -/
theorem exists_of_eq {A' : Protocol P I} (h : A = A') (ρ : Run A) :
    ∃ ρ' : Run A', ρ'.faulty = ρ.faulty ∧ ρ'.gst = ρ.gst ∧ ρ'.history = ρ.history ∧
      (∀ t δ, ρ'.Valid t δ ↔ ρ.Valid t δ) ∧
      ∀ (size : A'.Msg → ℕ) p a b, ρ'.bitsSent size p a b =
        ρ.bitsSent (fun m => size (cast (congrArg Protocol.Msg h) m)) p a b := by
  subst h
  exact ⟨ρ, rfl, rfl, rfl, fun _ _ => Iff.rfl, fun _ _ _ _ => rfl⟩

end Run

/-! ### Bits sent by composite protocols -/

section Compose

variable {I : Interface} {ι : Type} {J : ι → Interface} {L : Protocol P (I.uses J)}
  {C : (i : ι) → Protocol P (J i)}

variable (L C) in
/-- The sizes of the messages of the composite `L.compose C`, given the sizes `sizeL` of the
messages of the logic and `sizeC i` of the messages of child `i`. If the composite tags messages
with the component they belong to, the bits of the tag are part of these sizes. -/
def Compose.msgSize (sizeL : L.Msg → ℕ) (sizeC : (i : ι) → (C i).Msg → ℕ) :
    Compose.Msg L C → ℕ
  | .inl m => sizeL m
  | .inr ⟨i, m⟩ => sizeC i m

@[simp] theorem Compose.msgSize_inl (sizeL : L.Msg → ℕ) (sizeC : (i : ι) → (C i).Msg → ℕ)
    (m : L.Msg) : Compose.msgSize L C sizeL sizeC (.inl m) = sizeL m := rfl

@[simp] theorem Compose.msgSize_inr (sizeL : L.Msg → ℕ) (sizeC : (i : ι) → (C i).Msg → ℕ)
    (i : ι) (m : (C i).Msg) : Compose.msgSize L C sizeL sizeC (.inr ⟨i, m⟩) = sizeC i m := rfl

variable [DecidableEq ι]

/-- A sum over a list of elements of `α ⊕ Σ i, X i` splits into the sum over the left summands and
the sums over the fibres in a finite set `S` that contains every fibre with a nonzero sum. -/
private theorem sum_map_elim_eq {α : Type*} {X : ι → Type*} (f : α → ℕ) (g : (i : ι) → X i → ℕ)
    (S : Finset ι) (l : List (α ⊕ Σ i, X i))
    (hS : ∀ i ∉ S, ((l.filterMap (rightGet? i)).map (g i)).sum = 0) :
    (l.map (Sum.elim f fun e => g e.1 e.2)).sum =
      ((l.filterMap Sum.getLeft?).map f).sum +
        ∑ i ∈ S, ((l.filterMap (rightGet? i)).map (g i)).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    rcases e with a | ⟨j, x⟩
    · simp only [List.map_cons, List.sum_cons, Sum.elim_inl, List.filterMap_cons, Sum.getLeft?_inl,
        rightGet?_inl] at hS ⊢
      rw [ih hS]
      omega
    · have hcons : ∀ i, (((Sum.inr ⟨j, x⟩ :: l : List (α ⊕ Σ i, X i)).filterMap
          (rightGet? i)).map (g i)).sum =
          (if i = j then g j x else 0) + ((l.filterMap (rightGet? i)).map (g i)).sum := by
        intro i
        by_cases h : i = j
        · subst h
          simp
        · simp [sigmaGet?_mk_of_ne (Ne.symm h), h]
      simp only [hcons] at hS
      rw [List.map_cons, List.sum_cons, ih fun i hi => by have := hS i hi; omega,
        Finset.sum_congr rfl fun i _ => hcons i, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [List.filterMap_cons, Sum.getLeft?_inr, Sum.elim_inr]
      split_ifs with hj
      · omega
      · have := hS j hj
        simp only [↓reduceIte] at this
        omega

omit [DecidableEq ι] in
/-- The bits of the external outputs of a step of the logic are the bits of its outputs. -/
private theorem sum_bits_externalOutputs_inl (sizeL : L.Msg → ℕ)
    (sizeC : (i : ι) → (C i).Msg → ℕ) (os : List L.Out) :
    ((os.filterMap (Compose.liftLogic L C)).map
        (Output.bits (Compose.msgSize L C sizeL sizeC))).sum =
      (os.map (Output.bits sizeL)).sum := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    rcases o with ⟨q, m⟩ | (i | i) | ⟨k, T⟩ <;>
      simp [List.filterMap_cons, Compose.liftLogic, ih]

omit [DecidableEq ι] in
/-- The bits of the external outputs of a step of child `j` are the bits of its outputs. -/
private theorem sum_bits_externalOutputs_inr (sizeL : L.Msg → ℕ)
    (sizeC : (i : ι) → (C i).Msg → ℕ) (j : ι) (os : List (C j).Out) :
    ((os.filterMap (Compose.liftChild L C j)).map
        (Output.bits (Compose.msgSize L C sizeL sizeC))).sum =
      (os.map (Output.bits (sizeC j))).sum := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    rcases o with ⟨q, m⟩ | i | ⟨k, T⟩ <;>
      simp [List.filterMap_cons, Compose.liftChild, ih]

/-- The sum over a flattened list is the sum of the sums. -/
private theorem sum_map_flatMap {α β : Type*} (g : α → List β) (f : β → ℕ) (l : List α) :
    ((l.flatMap g).map f).sum = (l.map fun a => ((g a).map f).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

variable {ρ : Run (L.compose C)} {p : P} {a b : ℕ}
  {sizeL : L.Msg → ℕ} {sizeC : (i : ι) → (C i).Msg → ℕ}

/-- The bits sent by a process of the composite at time `τ` are the bits sent by its logic plus
the bits sent by its children in a finite set `S` that contains every child that sends bits at
time `τ`. -/
theorem Run.sum_bits_output_compose (S : Finset ι) (τ : ℕ)
    (hS : ∀ i ∉ S, (((ρ.child i).output p τ).map (Output.bits (sizeC i))).sum = 0) :
    ((ρ.output p τ).map (Output.bits (Compose.msgSize L C sizeL sizeC))).sum =
      ((ρ.logic.output p τ).map (Output.bits sizeL)).sum +
        ∑ i ∈ S, (((ρ.child i).output p τ).map (Output.bits (sizeC i))).sum := by
  rw [Run.output_compose, sum_map_flatMap]
  simp only [Run.output, Run.steps_logic, Run.steps_child, sum_map_flatMap] at hS ⊢
  have hF : (fun e => ((Compose.externalOutputs L C e).map
      (Output.bits (Compose.msgSize L C sizeL sizeC))).sum) =
      Sum.elim (fun a => (a.2.map (Output.bits sizeL)).sum)
        (fun e => (e.2.2.map (Output.bits (sizeC e.1))).sum) := by
    funext e
    rcases e with ⟨y, os⟩ | ⟨j, y, os⟩
    · exact sum_bits_externalOutputs_inl sizeL sizeC os
    · exact sum_bits_externalOutputs_inr sizeL sizeC j os
  rw [hF]
  exact sum_map_elim_eq _ (fun i (a : (C i).In × List (C i).Out) =>
    (a.2.map (Output.bits (sizeC i))).sum) S _ hS

/-- **Bits of a composite.** The bits sent by a process of the composite in a window are the bits
sent by its logic plus the bits sent by its children in a finite set `S` that contains every
child that sends bits in the window. -/
theorem Run.bitsSent_compose (S : Finset ι)
    (hS : ∀ i ∉ S, (ρ.child i).bitsSent (sizeC i) p a b = 0) :
    ρ.bitsSent (Compose.msgSize L C sizeL sizeC) p a b =
      ρ.logic.bitsSent sizeL p a b + ∑ i ∈ S, (ρ.child i).bitsSent (sizeC i) p a b := by
  simp only [bitsSent_eq_sum_Ico] at hS ⊢
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ hτ => Run.sum_bits_output_compose S τ fun i hi => ?_
  exact (Finset.sum_eq_zero_iff.1 (hS i hi)) τ hτ

/-- **Bits of a composite with finitely many children**: the bits sent by its logic plus the bits
sent by its children. -/
theorem Run.bitsSent_compose_univ [Fintype ι] :
    ρ.bitsSent (Compose.msgSize L C sizeL sizeC) p a b =
      ρ.logic.bitsSent sizeL p a b + ∑ i, (ρ.child i).bitsSent (sizeC i) p a b :=
  Run.bitsSent_compose Finset.univ fun i hi => absurd (Finset.mem_univ i) hi

end Compose

end Cslib.Distributed
