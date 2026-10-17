/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.NormNum

/-!
# Deterministic two-party communication protocols

Protocol trees in the sense of Kushilevitz–Nisan, *Communication Complexity*, Ch. 1. At an internal
node owned by Alice (resp. Bob), the owner sends one of `m` symbols computed from her (his) own
input only; the history is encoded in the position in the tree. Sending a symbol from an alphabet of
size `m` costs `⌈log₂ m⌉` bits (`Nat.clog 2 m`), so binary protocol trees are the case `m = 2`.

* `Protocol X Y α`, `Protocol.eval`, and the cost bound `Protocol.CostLE P c` ("every leaf of `P`
  is reached after at most `c` bits").
* `Protocol.card_le_of_fooling`: the **fooling-set bound** — a fooling set for the function
  computed by a protocol of cost `≤ c` has at most `2 ^ c` elements.
* `Protocol.disj_lowerBound`: the deterministic communication complexity of set disjointness
  `DISJ_K` is at least `K` (fooling set `{(S, Sᶜ)}`), i.e. `CC(DISJ_K) = Ω(K)` [KN, Example 1.23].
-/

@[expose] public section

namespace Cslib.CommunicationComplexity

/-- A deterministic two-party protocol tree with output in `α`. -/
inductive Protocol (X Y α : Type*) where
  /-- Stop and output `a`. -/
  | ret (a : α) : Protocol X Y α
  /-- Alice sends a symbol `f x : Fin m` and the protocol continues with `k (f x)`. -/
  | alice (m : ℕ) (f : X → Fin m) (k : Fin m → Protocol X Y α) : Protocol X Y α
  /-- Bob sends a symbol `g y : Fin m` and the protocol continues with `k (g y)`. -/
  | bob (m : ℕ) (g : Y → Fin m) (k : Fin m → Protocol X Y α) : Protocol X Y α

namespace Protocol

variable {X Y α : Type*}

/-- The output of a protocol on inputs `x` (Alice) and `y` (Bob). -/
def eval : Protocol X Y α → X → Y → α
  | ret a, _, _ => a
  | alice _ f k, x, y => eval (k (f x)) x y
  | bob _ g k, x, y => eval (k (g y)) x y

/-- `CostLE P c`: on every input, `P` exchanges at most `c` bits (a symbol of an `m`-letter
alphabet costs `⌈log₂ m⌉` bits). -/
def CostLE : Protocol X Y α → ℕ → Prop
  | ret _, _ => True
  | alice m _ k, c => Nat.clog 2 m ≤ c ∧ ∀ i, CostLE (k i) (c - Nat.clog 2 m)
  | bob m _ k, c => Nat.clog 2 m ≤ c ∧ ∀ i, CostLE (k i) (c - Nat.clog 2 m)

/-- A cost bound can be weakened. -/
theorem CostLE.mono : ∀ {P : Protocol X Y α} {c d : ℕ}, CostLE P c → c ≤ d → CostLE P d
  | ret _, _, _, _, _ => trivial
  | alice _ _ _, _, _, ⟨h1, h2⟩, hcd =>
      ⟨h1.trans hcd, fun i => CostLE.mono (h2 i) (Nat.sub_le_sub_right hcd _)⟩
  | bob _ _ _, _, _, ⟨h1, h2⟩, hcd =>
      ⟨h1.trans hcd, fun i => CostLE.mono (h2 i) (Nat.sub_le_sub_right hcd _)⟩

/-- Post-process the output of a protocol (no extra communication). -/
def map {β : Type*} (g : α → β) : Protocol X Y α → Protocol X Y β
  | ret a => ret (g a)
  | alice m f k => alice m f fun i => map g (k i)
  | bob m f k => bob m f fun i => map g (k i)

/-- Post-processing the output of a protocol post-processes its value. -/
@[simp] theorem eval_map {β : Type*} (g : α → β) :
    ∀ (P : Protocol X Y α) (x : X) (y : Y), (P.map g).eval x y = g (P.eval x y)
  | ret _, _, _ => rfl
  | alice _ f k, x, y => eval_map g (k (f x)) x y
  | bob _ f k, x, y => eval_map g (k (f y)) x y

/-- Post-processing the output does not change the cost. -/
theorem CostLE.map {β : Type*} (g : α → β) :
    ∀ {P : Protocol X Y α} {c : ℕ}, P.CostLE c → (P.map g).CostLE c
  | ret _, _, _ => trivial
  | alice _ _ _, _, ⟨h1, h2⟩ => ⟨h1, fun i => CostLE.map g (h2 i)⟩
  | bob _ _ _, _, ⟨h1, h2⟩ => ⟨h1, fun i => CostLE.map g (h2 i)⟩

/-- `P` computes `f`. -/
def Computes (P : Protocol X Y α) (f : X → Y → α) : Prop := ∀ x y, P.eval x y = f x y

/-- A **fooling set** for `f` with value `z`: all pairs have value `z`, and for two different pairs
one of the two "crossed" pairs has a value different from `z`. -/
def IsFooling (f : X → Y → α) (z : α) (S : Finset (X × Y)) : Prop :=
  (∀ s ∈ S, f s.1 s.2 = z) ∧
    ∀ s ∈ S, ∀ t ∈ S, s ≠ t → f s.1 t.2 ≠ z ∨ f t.1 s.2 ≠ z

/-- Splitting a finset along a function into `Fin m`: `#S ≤ m · max fibre`. -/
private lemma card_le_of_fibres {ι : Type*} {m : ℕ} (S : Finset ι) (g : ι → Fin m) (b : ℕ)
    (h : ∀ i : Fin m, (S.filter (fun s => g s = i)).card ≤ b) : S.card ≤ m * b := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ) (by intro _ _; simp)]
  calc ∑ i ∈ (Finset.univ : Finset (Fin m)), (S.filter (fun s => g s = i)).card
      ≤ ∑ _i ∈ (Finset.univ : Finset (Fin m)), b := Finset.sum_le_sum fun i _ => h i
    _ = m * b := by simp

/-- Splitting the budget `c` into the cost of one symbol and the rest. -/
private lemma mul_pow_sub_le {m c : ℕ} (h : Nat.clog 2 m ≤ c) :
    m * 2 ^ (c - Nat.clog 2 m) ≤ 2 ^ c := by
  calc m * 2 ^ (c - Nat.clog 2 m) ≤ 2 ^ Nat.clog 2 m * 2 ^ (c - Nat.clog 2 m) :=
        Nat.mul_le_mul_right _ (Nat.le_pow_clog (by norm_num) m)
    _ = 2 ^ c := by rw [← pow_add, Nat.add_sub_cancel' h]

/-- **Fooling-set bound** (Kushilevitz–Nisan, Lemma 1.20): if `P` has cost at most `c`, every
fooling set for the function computed by `P` has at most `2 ^ c` elements. -/
theorem card_le_of_fooling :
    ∀ (P : Protocol X Y α) (c : ℕ) (z : α) (S : Finset (X × Y)),
      P.CostLE c → IsFooling P.eval z S → S.card ≤ 2 ^ c
  | ret a, c, z, S, _, ⟨h1, h2⟩ => by
      refine le_trans (Finset.card_le_one.2 fun s hs t ht => ?_) (Nat.one_le_two_pow)
      by_contra hst
      rcases h2 s hs t ht hst with h | h <;> exact h (by simpa [eval] using h1 s hs)
  | alice m f k, c, z, S, ⟨hc, hk⟩, ⟨h1, h2⟩ => by
      refine le_trans (card_le_of_fibres S (fun s => f s.1) (2 ^ (c - Nat.clog 2 m))
        fun i => ?_) (mul_pow_sub_le hc)
      refine card_le_of_fooling (k i) _ z _ (hk i) ⟨fun s hs => ?_, fun s hs t ht hst => ?_⟩
      · rw [Finset.mem_filter] at hs
        have := h1 s hs.1
        simp only [eval, hs.2] at this
        exact this
      · rw [Finset.mem_filter] at hs ht
        have := h2 s hs.1 t ht.1 hst
        simp only [eval, hs.2, ht.2] at this
        exact this
  | bob m g k, c, z, S, ⟨hc, hk⟩, ⟨h1, h2⟩ => by
      refine le_trans (card_le_of_fibres S (fun s => g s.2) (2 ^ (c - Nat.clog 2 m))
        fun i => ?_) (mul_pow_sub_le hc)
      refine card_le_of_fooling (k i) _ z _ (hk i) ⟨fun s hs => ?_, fun s hs t ht hst => ?_⟩
      · rw [Finset.mem_filter] at hs
        have := h1 s hs.1
        simp only [eval, hs.2] at this
        exact this
      · rw [Finset.mem_filter] at hs ht
        have := h2 s hs.1 t ht.1 hst
        simp only [eval, hs.2, ht.2] at this
        exact this

/-- Fooling-set bound, stated for a protocol computing a given function `f`. -/
theorem card_le_of_fooling' {P : Protocol X Y α} {c : ℕ}
    {f : X → Y → α} (hP : P.Computes f) (hc : P.CostLE c) {z : α} {S : Finset (X × Y)}
    (hS : IsFooling f z S) : S.card ≤ 2 ^ c := by
  have : P.eval = f := funext fun x => funext fun y => hP x y
  exact card_le_of_fooling P c z S hc (this ▸ hS)

/-- Set disjointness `DISJ_K` on index set `ι` (`|ι| = K`): `true` iff there is no `i` with
`x i = y i = true`. -/
def disj {ι : Type*} [Fintype ι] (x y : ι → Bool) : Bool :=
  decide (∀ i, ¬(x i = true ∧ y i = true))

/-- **Deterministic communication complexity of set disjointness**: every deterministic protocol
computing `DISJ_K` exchanges at least `K` bits on some input (`CC(DISJ_K) ≥ K`). -/
theorem disj_lowerBound {ι : Type*} [Fintype ι] {P : Protocol (ι → Bool) (ι → Bool) Bool}
    {c : ℕ} (hP : P.Computes disj) (hc : P.CostLE c) : Fintype.card ι ≤ c := by
  classical
  let S : Finset ((ι → Bool) × (ι → Bool)) :=
    Finset.univ.image fun x : ι → Bool => (x, fun i => !x i)
  have hinj : Function.Injective fun x : ι → Bool => (x, fun i => !x i) :=
    fun a b h => (Prod.ext_iff.1 h).1
  have hcard : S.card = 2 ^ Fintype.card ι := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool]
  have hfool : IsFooling disj true S := by
    refine ⟨fun s hs => ?_, fun s hs t ht hst => ?_⟩
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hs
      simp [disj]
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨x', -, rfl⟩ := Finset.mem_image.1 ht
      have hx : x ≠ x' := fun h => hst (by rw [h])
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
      cases hxi : x i <;> cases hx'i : x' i <;>
        simp_all only [ne_eq, Prod.mk.injEq, false_and, not_false_eq_true, not_true_eq_false,
          Bool.false_eq_true, Bool.true_eq_false, disj, Bool.not_eq_eq_eq_not, Bool.not_true,
          not_and, Bool.not_eq_false, decide_eq_true_eq, not_forall, Bool.not_eq_true]
      · exact Or.inr ⟨i, hx'i, hxi⟩
      · exact Or.inl ⟨i, hxi, hx'i⟩
  have := card_le_of_fooling' hP hc hfool
  rw [hcard] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

/-- The complement of set disjointness ("the sets intersect") has the same deterministic
communication complexity: at least `K`. -/
theorem not_disj_lowerBound {ι : Type*} [Fintype ι]
    {P : Protocol (ι → Bool) (ι → Bool) Bool} {c : ℕ}
    (hP : P.Computes fun x y => !disj x y) (hc : P.CostLE c) : Fintype.card ι ≤ c :=
  disj_lowerBound (P := P.map not) (fun x y => by simp [eval_map, hP x y]) (hc.map not)

/-- Robust form: a protocol that is only required to answer "the sets intersect" correctly when
at least one of the two inputs is non-zero still needs `K` bits. (Lower-bound graphs are often
disconnected exactly when `x = y = 0`; this covers algorithms that only work on connected
graphs.) -/
theorem not_disj_lowerBound_of_ne_zero {ι : Type*} [Fintype ι]
    {P : Protocol (ι → Bool) (ι → Bool) Bool} {c : ℕ}
    (hP : ∀ x y, ((∃ i, x i = true) ∨ ∃ i, y i = true) → P.eval x y = !disj x y)
    (hc : P.CostLE c) : Fintype.card ι ≤ c := by
  classical
  by_cases hι : IsEmpty ι
  · simp
  obtain ⟨i₀⟩ := not_isEmpty_iff.1 hι
  let S : Finset ((ι → Bool) × (ι → Bool)) :=
    Finset.univ.image fun x : ι → Bool => (x, fun i => !x i)
  have hinj : Function.Injective fun x : ι → Bool => (x, fun i => !x i) :=
    fun a b h => (Prod.ext_iff.1 h).1
  have hcard : S.card = 2 ^ Fintype.card ι := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool]
  have hfool : IsFooling P.eval false S := by
    refine ⟨fun s hs => ?_, fun s hs t ht hst => ?_⟩
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hs
      have hnz : (∃ i, x i = true) ∨ ∃ i, (fun i => !x i) i = true := by
        cases h : x i₀
        · exact Or.inr ⟨i₀, by simp [h]⟩
        · exact Or.inl ⟨i₀, h⟩
      rw [hP x _ hnz]
      simp [disj]
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨x', -, rfl⟩ := Finset.mem_image.1 ht
      have hx : x ≠ x' := fun h => hst (by rw [h])
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
      by_cases hxi : x i = true
      · have hx'i : x' i = false := by
          cases h : x' i
          · rfl
          · exact absurd (hxi.trans h.symm) hi
        left
        rw [hP x _ (Or.inl ⟨i, hxi⟩)]
        intro h
        simp only [disj, Bool.not_eq_false', decide_eq_true_eq] at h
        exact h i ⟨hxi, by simp [hx'i]⟩
      · have hxi' : x i = false := by simpa using hxi
        have hx'i : x' i = true := by
          cases h : x' i
          · exact absurd (hxi'.trans h.symm) hi
          · rfl
        right
        rw [hP x' _ (Or.inl ⟨i, hx'i⟩)]
        intro h
        simp only [disj, Bool.not_eq_false', decide_eq_true_eq] at h
        exact h i ⟨hx'i, by simp [hxi']⟩
  have := card_le_of_fooling P c false S hc hfool
  rw [hcard] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

end Protocol

end Cslib.CommunicationComplexity
