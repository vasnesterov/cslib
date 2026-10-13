/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Arrovian social choice: preferences, aggregation maps, Arrow's axioms

## Main definitions

* `Pref X`: strict total orders ("preferences") on a type of alternatives `X`, as a bundled
  relation `P a b` = "`a` is ranked strictly higher than `b`". `X` may be infinite.
* `Pref.ofRank p`: the preference ranking by a priority `p : X → ℕ` (smaller is better), ties broken
  by a fixed well-order of `X`. This is the workhorse for building profiles with prescribed
  pairwise comparisons.
* `Pref.restrict`, `Pref.extend`: restriction to / extension from a subset.
* Aggregation maps (social welfare functions) `F : (ι → Pref X) → Pref X` on profiles over
  voters `ι`, and the axioms `Unanimity`, `IIA` (independence of irrelevant alternatives),
  `IsDictator`, `Dictatorial`, also relativised to a domain `D` of admissible profiles
  (`UnanimityOn`, `IIAOn`, `IsDictatorOn`).
* `ArrowHolds ι X`: "every unanimous IIA aggregation map is dictatorial" (the statement of Arrow's
  impossibility theorem for voters `ι` and alternatives `X`).

## References

* K. J. Arrow, *A difficulty in the concept of social welfare*, Journal of Political Economy 58
  (1950).
-/

@[expose] public section

namespace Cslib.SocialChoice

/-- A preference: a strict total order on the alternatives `X`. `P a b` means that `a` is ranked
strictly higher than `b`. -/
@[ext]
structure Pref (X : Type*) where
  /-- `P a b`: `a` is strictly preferred to `b`. -/
  P : X → X → Prop
  /-- No alternative is strictly preferred to itself. -/
  irrefl : ∀ a, ¬ P a a
  /-- Strict preference is transitive. -/
  trans : ∀ {a b c}, P a b → P b c → P a c
  /-- Any two distinct alternatives are comparable. -/
  total : ∀ {a b}, a ≠ b → P a b ∨ P b a

namespace Pref

variable {X : Type*} (R : Pref X) {a b c : X}

theorem asymm (h : R.P a b) : ¬ R.P b a := fun h' => R.irrefl a (R.trans h h')

theorem ne_of_P (h : R.P a b) : a ≠ b := by rintro rfl; exact R.irrefl a h

theorem not_P_iff (hab : a ≠ b) : ¬ R.P a b ↔ R.P b a :=
  ⟨fun h => (R.total hab).resolve_left h, fun h => R.asymm h⟩

/-- Two preferences that agree on all pairs are equal. -/
theorem ext_iff' {R S : Pref X} : R = S ↔ ∀ a b, R.P a b ↔ S.P a b := by
  constructor
  · rintro rfl; simp
  · intro h; ext a b; exact h a b

/-- If two preferences agree on `a` vs `b` (one direction), they agree in both directions. -/
theorem P_swap_iff {R S : Pref X} (hab : a ≠ b) (h : R.P a b ↔ S.P a b) :
    R.P b a ↔ S.P b a := by
  rw [← R.not_P_iff hab, ← S.not_P_iff hab, h]

/-- The preference ranking alternatives by a priority `p` (smaller value = more preferred), ties
broken by a fixed well-order of `X`. -/
noncomputable def ofRank (p : X → ℕ) : Pref X where
  P a b := p a < p b ∨ (p a = p b ∧ WellOrderingRel a b)
  irrefl a := by
    rintro (h | ⟨-, h⟩)
    · exact lt_irrefl _ h
    · exact irrefl_of WellOrderingRel a h
  trans := by
    intro a b c h1 h2
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (e2 ▸ h1)
    · exact Or.inl (e1 ▸ h2)
    · exact Or.inr ⟨e1.trans e2, trans_of WellOrderingRel h1 h2⟩
  total := by
    intro a b hab
    rcases lt_trichotomy (p a) (p b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases trichotomous_of WellOrderingRel a b with
        h' | h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact absurd h' hab
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inr (Or.inl h)

theorem ofRank_P_def (p : X → ℕ) (a b : X) :
    (ofRank p).P a b ↔ p a < p b ∨ (p a = p b ∧ WellOrderingRel a b) := Iff.rfl

theorem ofRank_P_of_lt {p : X → ℕ} (h : p a < p b) : (ofRank p).P a b := Or.inl h

theorem ofRank_P_iff {p : X → ℕ} (h : p a ≠ p b) : (ofRank p).P a b ↔ p a < p b := by
  constructor
  · rintro (h' | ⟨h', -⟩)
    · exact h'
    · exact absurd h' h
  · exact Or.inl

/-- There is a preference ranking `a` above `b` (for `a ≠ b`). -/
theorem exists_P (hab : a ≠ b) : ∃ R : Pref X, R.P a b := by
  classical
  exact ⟨ofRank (fun x => if x = a then 0 else 1), ofRank_P_of_lt (by simp [hab.symm])⟩

/-- Restriction of a preference to a subset. -/
def restrict (S : Set X) : Pref S where
  P a b := R.P a b
  irrefl a := R.irrefl a
  trans h1 h2 := R.trans h1 h2
  total h := R.total (fun e => h (Subtype.ext e))

/-- Extension of a preference on a subset `S` to all of `X`: the elements of `S` (ordered by `R`)
come first, then the others (ordered by a fixed well-order). -/
noncomputable def extend {S : Set X} (R : Pref S) : Pref X where
  P a b := (∃ (ha : a ∈ S) (hb : b ∈ S), R.P ⟨a, ha⟩ ⟨b, hb⟩) ∨ (a ∈ S ∧ b ∉ S) ∨
    (a ∉ S ∧ b ∉ S ∧ WellOrderingRel a b)
  irrefl a := by
    rintro (⟨ha, hb, h⟩ | ⟨h1, h2⟩ | ⟨-, -, h⟩)
    · exact R.irrefl _ h
    · exact h2 h1
    · exact irrefl_of WellOrderingRel a h
  trans := by
    intro a b c h1 h2
    rcases h1 with ⟨ha, hb, h1⟩ | ⟨ha, hb⟩ | ⟨ha, hb, h1⟩ <;>
      rcases h2 with ⟨hb', hc, h2⟩ | ⟨hb', hc⟩ | ⟨hb', hc, h2⟩
    · exact Or.inl ⟨ha, hc, R.trans h1 h2⟩
    · exact Or.inr (Or.inl ⟨ha, hc⟩)
    · exact absurd hb hb'
    all_goals first
      | exact absurd hb' hb
      | exact Or.inr (Or.inl ⟨ha, hc⟩)
      | exact Or.inr (Or.inr ⟨ha, hc,
          trans_of WellOrderingRel h1 h2⟩)
  total := by
    intro a b hab
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · rcases R.total (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (fun e => hab (congrArg Subtype.val e)) with
        h | h
      · exact Or.inl (Or.inl ⟨ha, hb, h⟩)
      · exact Or.inr (Or.inl ⟨hb, ha, h⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨ha, hb⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hb, ha⟩))
    · rcases trichotomous_of WellOrderingRel a b with
        h | h | h
      · exact Or.inl (Or.inr (Or.inr ⟨ha, hb, h⟩))
      · exact absurd h hab
      · exact Or.inr (Or.inr (Or.inr ⟨hb, ha, h⟩))

theorem extend_P_iff {S : Set X} (R : Pref S) (a b : S) :
    R.extend.P a b ↔ R.P a b := by
  constructor
  · rintro (⟨ha, hb, h⟩ | ⟨-, h⟩ | ⟨h, -⟩)
    · exact h
    · exact absurd b.2 h
    · exact absurd a.2 h
  · intro h; exact Or.inl ⟨a.2, b.2, h⟩

theorem restrict_extend {S : Set X} (R : Pref S) : R.extend.restrict S = R := by
  ext a b; exact extend_P_iff R a b

end Pref

variable {ι X : Type*}

/-- A profile: one preference per voter. -/
abbrev Profile (ι X : Type*) := ι → Pref X

/-- An aggregation map (social welfare function). -/
abbrev Aggregation (ι X : Type*) := Profile ι X → Pref X

/-- Unanimity (Pareto): if every voter ranks `a` above `b`, so does society. -/
def Unanimity (F : Aggregation ι X) : Prop :=
  ∀ (R : Profile ι X) (a b : X), (∀ i, (R i).P a b) → (F R).P a b

/-- Independence of irrelevant alternatives: the social ranking of `a` vs `b` only depends on the
individual rankings of `a` vs `b`. -/
def IIA (F : Aggregation ι X) : Prop :=
  ∀ (R S : Profile ι X) (a b : X), (∀ i, ((R i).P a b ↔ (S i).P a b)) →
    ((F R).P a b ↔ (F S).P a b)

/-- Voter `k` is a dictator: society always follows `k`'s strict preferences. -/
def IsDictator (F : Aggregation ι X) (k : ι) : Prop :=
  ∀ (R : Profile ι X) (a b : X), (R k).P a b → (F R).P a b

/-- `F` has a dictator. -/
def Dictatorial (F : Aggregation ι X) : Prop := ∃ k, IsDictator F k

/-- Arrow's impossibility theorem for voters `ι` and alternatives `X`: every unanimous aggregation
map satisfying IIA is dictatorial. -/
def ArrowHolds (ι X : Type*) : Prop :=
  ∀ F : Aggregation ι X, Unanimity F → IIA F → Dictatorial F

theorem isDictator_iff_eq (F : Aggregation ι X) (k : ι) :
    IsDictator F k ↔ ∀ R, F R = R k := by
  constructor
  · intro h R
    ext a b
    constructor
    · intro hab
      by_contra hn
      have hne : a ≠ b := (F R).ne_of_P hab
      exact (F R).asymm hab (h R b a (((R k).not_P_iff hne).1 hn))
    · exact h R a b
  · intro h R a b hab; rw [h R]; exact hab

/-! ### Restricted domains -/

/-- Unanimity on a domain `D` of admissible profiles (`F` is only relevant on `D`). -/
def UnanimityOn (D : Set (Profile ι X)) (F : Aggregation ι X) : Prop :=
  ∀ R ∈ D, ∀ a b : X, (∀ i, (R i).P a b) → (F R).P a b

/-- IIA on a domain `D`. -/
def IIAOn (D : Set (Profile ι X)) (F : Aggregation ι X) : Prop :=
  ∀ R ∈ D, ∀ S ∈ D, ∀ a b : X, (∀ i, ((R i).P a b ↔ (S i).P a b)) →
    ((F R).P a b ↔ (F S).P a b)

/-- Voter `k` is a dictator on the domain `D`. -/
def IsDictatorOn (D : Set (Profile ι X)) (F : Aggregation ι X) (k : ι) : Prop :=
  ∀ R ∈ D, ∀ a b : X, (R k).P a b → (F R).P a b

/-- The domain `D` admits a unanimous, IIA, non-dictatorial aggregation map. -/
def AdmitsNonDictatorial (D : Set (Profile ι X)) : Prop :=
  ∃ F : Aggregation ι X, UnanimityOn D F ∧ IIAOn D F ∧ ∀ k, ¬ IsDictatorOn D F k

theorem unanimityOn_univ (F : Aggregation ι X) : UnanimityOn Set.univ F ↔ Unanimity F := by
  simp [UnanimityOn, Unanimity]

theorem iiaOn_univ (F : Aggregation ι X) : IIAOn Set.univ F ↔ IIA F := by
  simp [IIAOn, IIA]

theorem isDictatorOn_univ (F : Aggregation ι X) (k : ι) :
    IsDictatorOn Set.univ F k ↔ IsDictator F k := by
  simp [IsDictatorOn, IsDictator]

end Cslib.SocialChoice
