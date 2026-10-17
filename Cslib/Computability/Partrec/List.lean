/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.Primrec.List

/-!
# Computable list combinators

Mathlib proves closure of `Primrec` under `List.foldl`, `List.map`, … only for *primitive
recursive* step functions (`Primrec.list_foldl`, `Primrec.list_map`, …). Here we prove the
`Computable` versions, for step functions that are merely computable, via `Computable.nat_rec`
over list indices:

* `Computable.list_foldl`, `Computable.list_map`, `Computable.list_all`, `Computable.list_any`,
  `Computable.list_findSome?`, `Computable.list_filterMap`, `Computable.list_flatMap`,
  `Computable.list_filter`;
* `Computable.nat_find`: unbounded search for the least witness of a computable, everywhere
  satisfiable predicate.
-/

@[expose] public section

namespace Computable

variable {α β σ γ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ] [Primcodable γ]

/-- One step of folding a list by iterating over its indices. -/
private def foldStep (l : List β) (h : σ → β → σ) (y : ℕ) (IH : σ) : σ :=
  match l[y]? with
  | some b => h IH b
  | none => IH

omit [Primcodable β] [Primcodable σ] in
/-- Folding a list by iterating over its indices. -/
private theorem foldl_eq_rec (l : List β) (h : σ → β → σ) (s : σ) (i : ℕ) :
    (l.take i).foldl h s = Nat.rec (motive := fun _ => σ) s (foldStep l h) i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.take_add_one, List.foldl_append, ih]
    simp only [foldStep]
    cases l[i]? <;> rfl

/-- `List.foldl` with a computable step function is computable. -/
theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  have hs : Computable₂ fun (a : α) (p : ℕ × σ) =>
      foldStep (f a) (fun s b => h a (s, b)) p.1 p.2 := by
    refine (option_casesOn (g := fun (q : α × ℕ × σ) b => h q.1 (q.2.2, b))
      (list_getElem?.comp (hf.comp fst) (fst.comp snd)) (snd.comp snd)
      ?_).to₂.of_eq ?_
    · exact (hh.comp (fst.comp fst) (pair (snd.comp (snd.comp fst)) snd)).to₂
    · intro p; simp only [foldStep]; cases (f p.1)[p.2.1]? <;> rfl
  refine (nat_rec (list_length.comp hf) hg hs).of_eq fun a => ?_
  rw [← List.take_length (l := f a), foldl_eq_rec, List.take_length]

/-- `List.map` with a computable function is computable. -/
theorem list_map {f : α → List β} {g : α → β → σ} (hf : Computable f)
    (hg : Computable₂ g) : Computable fun a => (f a).map (g a) := by
  have h := list_foldl (f := f) (g := fun _ => ([] : List σ))
    (h := fun a p => p.1 ++ [g a p.2]) hf (const _)
    ((list_concat.comp (fst.comp snd) (hg.comp fst (snd.comp snd))).to₂)
  refine h.of_eq fun a => ?_
  suffices ∀ (l : List β) (acc : List σ),
      l.foldl (fun s b => s ++ [g a b]) acc = acc ++ l.map (g a) by simpa using this (f a) []
  intro l
  induction l with
  | nil => simp
  | cons b l ih => intro acc; simp [ih]

/-- `List.all` with a computable predicate is computable. -/
theorem list_all {f : α → List β} {p : α → β → Bool} (hf : Computable f)
    (hp : Computable₂ p) : Computable fun a => (f a).all (p a) := by
  have h := list_foldl (f := f) (g := fun _ => true)
    (h := fun a q => q.1 && p a q.2) hf (const _)
    ((Primrec.and.to_comp.comp (fst.comp snd) (hp.comp fst (snd.comp snd))).to₂)
  refine h.of_eq fun a => ?_
  suffices ∀ (l : List β) (acc : Bool),
      l.foldl (fun s b => s && p a b) acc = (acc && l.all (p a)) by simpa using this (f a) true
  intro l
  induction l with
  | nil => simp
  | cons b l ih => intro acc; simp [ih, Bool.and_assoc]

/-- `List.any` with a computable predicate is computable. -/
theorem list_any {f : α → List β} {p : α → β → Bool} (hf : Computable f)
    (hp : Computable₂ p) : Computable fun a => (f a).any (p a) := by
  have h := list_foldl (f := f) (g := fun _ => false)
    (h := fun a q => q.1 || p a q.2) hf (const _)
    ((Primrec.or.to_comp.comp (fst.comp snd) (hp.comp fst (snd.comp snd))).to₂)
  refine h.of_eq fun a => ?_
  suffices ∀ (l : List β) (acc : Bool),
      l.foldl (fun s b => s || p a b) acc = (acc || l.any (p a)) by simpa using this (f a) false
  intro l
  induction l with
  | nil => simp
  | cons b l ih => intro acc; simp [ih, Bool.or_assoc]

/-- `List.findSome?` with a computable function is computable. -/
theorem list_findSome? {f : α → List β} {g : α → β → Option σ} (hf : Computable f)
    (hg : Computable₂ g) : Computable fun a => (f a).findSome? (g a) := by
  have h := list_foldl (f := f) (g := fun _ => (none : Option σ))
    (h := fun a q => Option.casesOn q.1 (g a q.2) some) hf (const _)
    ((option_casesOn (fst.comp snd) (hg.comp fst (snd.comp snd))
      (option_some.comp snd).to₂).to₂)
  refine h.of_eq fun a => ?_
  suffices ∀ (l : List β) (acc : Option σ),
      l.foldl (fun s b => Option.casesOn s (g a b) some) acc =
        Option.casesOn acc (l.findSome? (g a)) some by simpa using this (f a) none
  intro l
  induction l with
  | nil => intro acc; cases acc <;> rfl
  | cons b l ih =>
    intro acc
    cases acc with
    | none =>
      simp only [List.foldl_cons, List.findSome?_cons]
      rw [ih]
      cases g a b <;> rfl
    | some x =>
      simp only [List.foldl_cons]
      rw [ih]

/-- `List.filterMap` with a computable function is computable. -/
theorem list_filterMap {f : α → List β} {g : α → β → Option σ} (hf : Computable f)
    (hg : Computable₂ g) : Computable fun a => (f a).filterMap (g a) := by
  have h := list_foldl (f := f) (g := fun _ => ([] : List σ))
    (h := fun a q => Option.casesOn (g a q.2) q.1 (fun c => q.1 ++ [c])) hf (const _)
    ((option_casesOn (hg.comp fst (snd.comp snd)) (fst.comp snd)
      (list_concat.comp (fst.comp (snd.comp fst)) snd).to₂).to₂)
  refine h.of_eq fun a => ?_
  suffices ∀ (l : List β) (acc : List σ),
      l.foldl (fun s b => Option.casesOn (g a b) s (fun c => s ++ [c])) acc =
        acc ++ l.filterMap (g a) by simpa using this (f a) []
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    intro acc
    simp only [List.foldl_cons, List.filterMap_cons]
    rw [ih]
    cases g a b <;> simp

/-- `List.flatMap` with a computable function is computable. -/
theorem list_flatMap {f : α → List β} {g : α → β → List σ} (hf : Computable f)
    (hg : Computable₂ g) : Computable fun a => (f a).flatMap (g a) := by
  have h := list_foldl (f := f) (g := fun _ => ([] : List σ))
    (h := fun a q => q.1 ++ g a q.2) hf (const _)
    ((list_append.comp (fst.comp snd) (hg.comp fst (snd.comp snd))).to₂)
  refine h.of_eq fun a => ?_
  suffices ∀ (l : List β) (acc : List σ),
      l.foldl (fun s b => s ++ g a b) acc = acc ++ l.flatMap (g a) by simpa using this (f a) []
  intro l
  induction l with
  | nil => simp
  | cons b l ih => intro acc; simp [ih]

/-- `List.filter` with a computable predicate is computable. -/
theorem list_filter {f : α → List β} {p : α → β → Bool} (hf : Computable f)
    (hp : Computable₂ p) : Computable fun a => (f a).filter (p a) := by
  refine (list_filterMap (g := fun a b => bif p a b then some b else none) hf
    (cond hp (option_some.comp snd) (const none)).to₂).of_eq fun a => ?_
  rw [← List.filterMap_eq_filter]
  congr 1
  funext b
  rcases h : p a b <;> simp [Option.guard, h]

/-- Unbounded search: the least witness of a computable, everywhere satisfiable predicate is a
computable function of the parameter. -/
theorem nat_find {p : α → ℕ → Bool} (hp : Computable₂ p) (h : ∀ a, ∃ n, p a n = true) :
    Computable fun a => Nat.find (h a) := by
  classical
  refine (Partrec.rfind (p := fun a n => (Part.some (p a n))) hp.partrec₂).of_eq fun a => ?_
  refine Part.eq_some_iff.mpr (Nat.mem_rfind.mpr ⟨?_, fun {m} hm => ?_⟩)
  · simp only [Part.mem_some_iff]; exact (Nat.find_spec (h a)).symm
  · simp only [Part.mem_some_iff]
    have := Nat.find_min (h a) hm
    simpa using this

end Computable
