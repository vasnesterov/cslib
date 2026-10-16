/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Order.SuccPred.Nat

/-!
# The free Coxeter group `G_k`

The group `G_k = ⟨1, …, k | 1², …, k²⟩` (free product of `k` copies of `ℤ/2`, the universal Coxeter
group). Its Cayley graph `Γ_k` with respect to the generators is the `k`-regular, `k`-edge-coloured
infinite tree; prefix-closed subsets of `G_k` are exactly the edge-coloured trees rooted at `e`
("colour systems", see `Cslib.ColourSystem.IsColourSystem`).

Elements are represented by **reduced words** (no two consecutive equal letters), stored **in
reverse**: the list `[c_l, …, c_1]` represents `c_1 c_2 ⋯ c_l`. So the head of the list is the last
letter (`tail` in the terminology of Hirvonen and Suomela [HirvonenSuomela2012]), and right
multiplication by a generator acts at the head of the list.

Main API: the group instance, generators `gen c`, the length `len x` (= `|x|`, distance to `e` in
`Γ_k`), `len_mul_gen` (`|xc| = |x| ± 1`), `eq_of_len_mul_gen_lt` (unique parent),
`startsWith c x` (the reduced word of `x` begins with `c`), and finiteness of balls.

Mathlib's `CoxeterMatrix.Group` gives the same group by a presentation (for the Coxeter matrix
with all off-diagonal entries `0`); the concrete normal form used here makes lengths, parents and
branches at `e` computable by list manipulations, which is what the tree arguments need. The two
are not formally identified.

## References

* [J. Hirvonen, J. Suomela, *Distributed maximal matching: greedy is optimal*][HirvonenSuomela2012]
-/

@[expose] public section

namespace Cslib.ColourSystem

/-- The free Coxeter group on `k` generators, as reduced words stored in reverse. -/
def FreeCox (k : ℕ) : Type := {l : List (Fin k) // l.IsChain (· ≠ ·)}

namespace FreeCox

variable {k : ℕ}

instance : DecidableEq (FreeCox k) := inferInstanceAs (DecidableEq {_l : List (Fin k) // _})

@[ext] theorem ext {x y : FreeCox k} (h : x.1 = y.1) : x = y := Subtype.ext h

/-! ### List-level operations -/

/-- Right multiplication of a (reversed) word by a generator, with cancellation. -/
def mulGenList : List (Fin k) → Fin k → List (Fin k)
  | [], c => [c]
  | a :: l, c => if a = c then l else c :: a :: l

theorem mulGenList_of_head_ne {l : List (Fin k)} {c : Fin k} (h : l.head? ≠ some c) :
    mulGenList l c = c :: l := by
  cases l with
  | nil => rfl
  | cons a l =>
    simp only [List.head?_cons, ne_eq, Option.some.injEq] at h
    simp [mulGenList, h]

theorem isChain_mulGenList {l : List (Fin k)} (hl : l.IsChain (· ≠ ·)) (c : Fin k) :
    (mulGenList l c).IsChain (· ≠ ·) := by
  cases l with
  | nil => simp [mulGenList]
  | cons a l =>
    simp only [mulGenList]
    split_ifs with h
    · exact hl.tail
    · exact List.IsChain.cons_cons (Ne.symm h) hl

theorem mulGenList_mulGenList {l : List (Fin k)} (hl : l.IsChain (· ≠ ·)) (c : Fin k) :
    mulGenList (mulGenList l c) c = l := by
  cases l with
  | nil => simp [mulGenList]
  | cons a l =>
    simp only [mulGenList]
    split_ifs with h
    · subst h
      cases l with
      | nil => simp
      | cons b l =>
        have hb : a ≠ b := (List.isChain_cons_cons.1 hl).1
        simp [Ne.symm hb]
    · simp

theorem length_mulGenList (l : List (Fin k)) (c : Fin k) :
    (mulGenList l c).length = l.length + 1 ∨ (mulGenList l c).length + 1 = l.length := by
  cases l with
  | nil => simp [mulGenList]
  | cons a l =>
    simp only [mulGenList]
    split_ifs <;> simp

/-- The action of a list of generators (processed from the last element to the first). -/
def act (x l : List (Fin k)) : List (Fin k) := l.foldr (fun c acc => mulGenList acc c) x

@[simp] theorem act_nil (x : List (Fin k)) : act x [] = x := rfl

@[simp] theorem act_cons (x l : List (Fin k)) (c : Fin k) :
    act x (c :: l) = mulGenList (act x l) c := rfl

theorem isChain_act {x : List (Fin k)} (hx : x.IsChain (· ≠ ·)) (l : List (Fin k)) :
    (act x l).IsChain (· ≠ ·) := by
  induction l with
  | nil => exact hx
  | cons c l ih => exact isChain_mulGenList ih c

theorem act_append (x l m : List (Fin k)) : act x (l ++ m) = act (act x m) l := by
  simp [act, List.foldr_append]

theorem act_mulGenList {x w : List (Fin k)} (hx : x.IsChain (· ≠ ·)) (hw : w.IsChain (· ≠ ·))
    (c : Fin k) : act x (mulGenList w c) = mulGenList (act x w) c := by
  cases w with
  | nil => rfl
  | cons a w =>
    by_cases h : a = c
    · subst h
      have : mulGenList (a :: w) a = w := by simp [mulGenList]
      rw [this, act_cons, mulGenList_mulGenList (isChain_act hx _)]
    · have : mulGenList (a :: w) c = c :: a :: w := by simp [mulGenList, h]
      rw [this]; rfl

theorem act_act {x y : List (Fin k)} (hx : x.IsChain (· ≠ ·)) (hy : y.IsChain (· ≠ ·))
    (l : List (Fin k)) : act x (act y l) = act (act x y) l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [act_cons, act_mulGenList hx (isChain_act hy l), ih, act_cons]

theorem act_nil_left {l : List (Fin k)} (hl : l.IsChain (· ≠ ·)) : act [] l = l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [act_cons, ih hl.tail]
    apply mulGenList_of_head_ne
    cases l with
    | nil => simp
    | cons b l =>
      have := (List.isChain_cons_cons.1 hl).1
      simpa [eq_comm] using this

theorem act_reverse {x : List (Fin k)} (hx : x.IsChain (· ≠ ·)) : act x x.reverse = [] := by
  induction x with
  | nil => rfl
  | cons c x ih =>
    rw [List.reverse_cons, act_append]
    simp only [act_cons, act_nil, mulGenList]
    exact ih hx.tail

/-- If `l ++ x` is reduced, acting by `l` on `x` does not cancel anything. -/
theorem act_of_isChain {x l : List (Fin k)} (h : (l ++ x).IsChain (· ≠ ·)) : act x l = l ++ x := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [act_cons, ih h.tail, List.cons_append]
    apply mulGenList_of_head_ne
    intro hc
    cases hlx : l ++ x with
    | nil => simp [hlx] at hc
    | cons b m =>
      rw [List.cons_append, hlx] at h
      simp [hlx] at hc
      exact (List.isChain_cons_cons.1 h).1 hc.symm

/-! ### The group -/

instance : One (FreeCox k) := ⟨⟨[], List.IsChain.nil⟩⟩
instance : Mul (FreeCox k) := ⟨fun x y => ⟨act x.1 y.1, isChain_act x.2 _⟩⟩
instance : Inv (FreeCox k) := ⟨fun x => ⟨x.1.reverse, List.isChain_reverse.2 (by
  simpa [flip, ne_comm] using x.2)⟩⟩

@[simp] theorem one_val : (1 : FreeCox k).1 = [] := rfl
theorem mul_val (x y : FreeCox k) : (x * y).1 = act x.1 y.1 := rfl
@[simp] theorem inv_val (x : FreeCox k) : x⁻¹.1 = x.1.reverse := rfl

instance : Group (FreeCox k) := Group.ofLeftAxioms
  (fun a b c => by ext1; simp only [mul_val]; exact (act_act a.2 b.2 c.1).symm)
  (fun a => by ext1; exact act_nil_left a.2)
  (fun a => by
    ext1
    simp only [mul_val, inv_val, one_val]
    have := act_reverse (x := a.1.reverse) (List.isChain_reverse.2 (by
      simpa [flip, ne_comm] using a.2))
    simpa using this)

/-- The generator `c`. -/
def gen (c : Fin k) : FreeCox k := ⟨[c], List.isChain_singleton c⟩

@[simp] theorem gen_val (c : Fin k) : (gen c).1 = [c] := rfl

theorem mul_gen_val (x : FreeCox k) (c : Fin k) : (x * gen c).1 = mulGenList x.1 c := rfl

@[simp] theorem gen_mul_gen (c : Fin k) : gen c * gen c = (1 : FreeCox k) := by
  ext1; simp [mul_gen_val, mulGenList]

@[simp] theorem inv_gen (c : Fin k) : (gen c)⁻¹ = gen c := by
  rw [inv_eq_iff_mul_eq_one, gen_mul_gen]

@[simp] theorem mul_gen_mul_gen (x : FreeCox k) (c : Fin k) : x * gen c * gen c = x := by
  rw [mul_assoc, gen_mul_gen, mul_one]

theorem gen_ne_one (c : Fin k) : gen c ≠ (1 : FreeCox k) := by
  intro h; have := congrArg Subtype.val h; simp at this

theorem gen_injective : Function.Injective (gen : Fin k → FreeCox k) := by
  intro a b h; have := congrArg Subtype.val h; simpa using this

@[simp] theorem gen_inj {a b : Fin k} : gen a = (gen b : FreeCox k) ↔ a = b :=
  gen_injective.eq_iff

/-! ### Length -/

/-- The length `|x|` of the reduced word of `x`: the distance from `e` to `x` in `Γ_k`. -/
def len (x : FreeCox k) : ℕ := x.1.length

@[simp] theorem len_one : len (1 : FreeCox k) = 0 := rfl
@[simp] theorem len_gen (c : Fin k) : len (gen c) = 1 := rfl

theorem len_eq_zero {x : FreeCox k} : len x = 0 ↔ x = 1 := by
  constructor
  · intro h; ext1; exact List.length_eq_zero_iff.1 h
  · rintro rfl; rfl

@[simp] theorem len_inv (x : FreeCox k) : len x⁻¹ = len x := by
  simp [len]

theorem len_mul_gen (x : FreeCox k) (c : Fin k) :
    len (x * gen c) = len x + 1 ∨ len (x * gen c) + 1 = len x :=
  length_mulGenList x.1 c

theorem len_mul_gen_lt_iff (x : FreeCox k) (c : Fin k) :
    len (x * gen c) < len x ↔ x.1.head? = some c := by
  unfold len
  rw [mul_gen_val]
  rcases hx : x.1 with _ | ⟨a, l⟩
  · simp [mulGenList]
  · simp only [mulGenList, List.head?_cons, Option.some.injEq]
    split_ifs with h <;> simp [h]

theorem len_mul_gen_of_lt {x : FreeCox k} {c : Fin k} (h : len (x * gen c) < len x) :
    len (x * gen c) + 1 = len x := by
  rcases len_mul_gen x c with h' | h' <;> omega

theorem len_mul_gen_of_not_lt {x : FreeCox k} {c : Fin k} (h : ¬ len (x * gen c) < len x) :
    len (x * gen c) = len x + 1 := by
  rcases len_mul_gen x c with h' | h' <;> omega

theorem len_mul_gen_ne (x : FreeCox k) (c : Fin k) : len (x * gen c) ≠ len x := by
  rcases len_mul_gen x c with h | h <;> omega

/-- Every node except `e` has a unique parent (neighbour closer to `e`). -/
theorem eq_of_len_mul_gen_lt {x : FreeCox k} {c c' : Fin k} (h : len (x * gen c) < len x)
    (h' : len (x * gen c') < len x) : c = c' := by
  rw [len_mul_gen_lt_iff] at h h'
  rw [h] at h'
  exact Option.some.inj h'

theorem exists_mul_gen_lt {x : FreeCox k} (hx : x ≠ 1) : ∃ c, len (x * gen c) < len x := by
  rcases hx' : x.1 with _ | ⟨a, l⟩
  · exact absurd (ext hx') hx
  · exact ⟨a, by rw [len_mul_gen_lt_iff, hx']; rfl⟩

theorem len_mul_le (x y : FreeCox k) : len (x * y) ≤ len x + len y := by
  unfold len
  rw [mul_val]
  generalize y.1 = l
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [act_cons]
    rcases length_mulGenList (act x.1 l) c with h | h <;> simp at * <;> omega

theorem len_mul_gen_le (x : FreeCox k) (c : Fin k) : len (x * gen c) ≤ len x + 1 := by
  rcases len_mul_gen x c with h | h <;> omega

theorem le_len_mul_gen (x : FreeCox k) (c : Fin k) : len x ≤ len (x * gen c) + 1 := by
  rcases len_mul_gen x c with h | h <;> omega

theorem len_gen_mul_le (x : FreeCox k) (c : Fin k) : len (gen c * x) ≤ len x + 1 := by
  have := len_mul_le (gen c) x; simp at this; omega

theorem le_len_gen_mul (x : FreeCox k) (c : Fin k) : len x ≤ len (gen c * x) + 1 := by
  have := len_gen_mul_le (gen c * x) c
  rw [← mul_assoc, gen_mul_gen, one_mul] at this
  exact this

/-- Induction along the tree: build `x` from `e` by moving away from `e`. -/
theorem induction_on {P : FreeCox k → Prop} (h1 : P 1)
    (hstep : ∀ x c, len x < len (x * gen c) → P x → P (x * gen c)) (x : FreeCox k) : P x := by
  induction hn : len x generalizing x with
  | zero => rw [len_eq_zero] at hn; subst hn; exact h1
  | succ n ih =>
    have hx : x ≠ 1 := by rintro rfl; simp at hn
    obtain ⟨c, hc⟩ := exists_mul_gen_lt hx
    have h1 := len_mul_gen_of_lt hc
    have := hstep (x * gen c) c (by rw [mul_gen_mul_gen]; omega) (ih _ (by omega))
    rwa [mul_gen_mul_gen] at this

/-! ### First letters -/

/-- `startsWith c x`: the reduced word of `x` begins with the letter `c`, i.e. the path from `e`
to `x` in `Γ_k` starts with the edge `{e, c}` (`head(x) = c` in [HirvonenSuomela2012]). -/
def startsWith (c : Fin k) (x : FreeCox k) : Prop := len (gen c * x) < len x

theorem startsWith_iff (c : Fin k) (x : FreeCox k) : startsWith c x ↔ x.1.getLast? = some c := by
  unfold startsWith
  have h1 : len (gen c * x) = len (x⁻¹ * gen c) := by
    rw [← len_inv, mul_inv_rev, inv_gen]
  rw [h1, ← len_inv x, len_mul_gen_lt_iff, inv_val, List.head?_reverse]

instance (c : Fin k) (x : FreeCox k) : Decidable (startsWith c x) :=
  inferInstanceAs (Decidable (_ < _))

@[simp] theorem not_startsWith_one (c : Fin k) : ¬ startsWith c (1 : FreeCox k) := by
  simp [startsWith_iff]

@[simp] theorem startsWith_gen {c c' : Fin k} : startsWith c (gen c') ↔ c' = c := by
  simp [startsWith_iff]

/-- The only edge of `Γ_k` between nodes starting with `c` and nodes not starting with `c` is
`{e, c}`. -/
theorem startsWith_mul_gen {c c' : Fin k} {x : FreeCox k}
    (h : startsWith c (x * gen c') ↔ ¬ startsWith c x) :
    c' = c ∧ (x = 1 ∨ x = gen c) := by
  rw [startsWith_iff, startsWith_iff, mul_gen_val] at h
  rcases hx : x.1 with _ | ⟨a, l⟩
  · rw [hx] at h
    simp only [mulGenList, List.getLast?_singleton, Option.some.injEq, List.getLast?_nil,
      reduceCtorEq, not_false_eq_true, iff_true] at h
    exact ⟨h, Or.inl (ext hx)⟩
  · rw [hx] at h
    simp only [mulGenList] at h
    split_ifs at h with hac
    · subst hac
      cases l with
      | nil =>
        simp only [List.getLast?_nil, reduceCtorEq, List.getLast?_singleton, Option.some.injEq,
          false_iff, Decidable.not_not] at h
        refine ⟨h, Or.inr (ext ?_)⟩
        rw [hx, h]; rfl
      | cons b l =>
        rw [List.getLast?_cons_cons] at h
        exact absurd h (by tauto)
    · rw [List.getLast?_cons_cons] at h
      exact absurd h (by tauto)

/-- No cancellation: if `x` starts with `c` and `y` does not, then `|ȳ x| = |y| + |x|`. -/
theorem len_inv_mul_of_startsWith {c : Fin k} {x y : FreeCox k} (hx : startsWith c x)
    (hy : ¬ startsWith c y) : len (y⁻¹ * x) = len y + len x := by
  rw [startsWith_iff] at hx hy
  have hchain : (x.1 ++ y.1.reverse).IsChain (· ≠ ·) := by
    rw [List.isChain_append]
    refine ⟨x.2, List.isChain_reverse.2 (by simpa [flip, ne_comm] using y.2), ?_⟩
    intro a ha b hb
    rw [hx] at ha
    rw [List.head?_reverse] at hb
    simp only [Option.mem_def, Option.some.injEq] at ha hb
    subst ha
    rintro rfl
    exact hy hb
  unfold len
  rw [mul_val, inv_val, act_of_isChain hchain]
  simp [Nat.add_comm]

/-! ### Balls are finite -/

theorem finite_len_le (R : ℕ) : {x : FreeCox k | len x ≤ R}.Finite := by
  have := (List.finite_length_le (Fin k) R).preimage
    (f := fun x : FreeCox k => x.1) (Subtype.val_injective.injOn)
  exact this

end FreeCox

end Cslib.ColourSystem
