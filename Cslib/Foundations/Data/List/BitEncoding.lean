/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Range
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Linarith
public import Cslib.Foundations.Data.Nat.CeilDiv

/-!
# Self-delimiting encoding of tuples of bit strings, and splitting into blocks

* `Cslib.BitEncoding.encList : List (List Bool) → List Bool` encodes a tuple of bit strings (every
  bit `b` becomes `true, b`, every string is terminated by `false`); `decList` decodes it
  (`decList_encList`), and `length_encList` gives the length `Σ (2|sᵢ| + 1)`. This is the "fixed
  delimiter scheme" used to pack several labels into one in proof-labelling/CONGEST label-size
  arguments.
* `Cslib.BitEncoding.chunk S L i` is the `i`-th block of length `L` of a list `S`; concatenating the
  blocks `0, …, k-1` with `L = ⌈|S|/k⌉` gives back `S` (`flatten_chunks`).
* `List.Nodup.map_idxOf`: mapping `u ↦ f (l.idxOf u)` over a duplicate-free `l` is mapping `f`
  over the indices.
-/

@[expose] public section

namespace Cslib.BitEncoding

/-- Encoding of one string, terminated by `false`. -/
def encStr (s : List Bool) : List Bool := s.flatMap (fun b => [true, b]) ++ [false]

/-- Encoding of a tuple of strings (the fixed delimiter scheme). -/
def encList (L : List (List Bool)) : List Bool := L.flatMap encStr

/-- Decoder with an accumulator (holding the reversed current string). -/
def decAux : List Bool → List Bool → List (List Bool)
  | _, [] => []
  | acc, false :: rest => acc.reverse :: decAux [] rest
  | acc, true :: b :: rest => decAux (b :: acc) rest
  | _, [true] => []

/-- Decoding of `encList`. -/
def decList (w : List Bool) : List (List Bool) := decAux [] w

/-- The decoder reads one encoded string and continues with the rest. -/
lemma decAux_encStr_append (acc s rest : List Bool) :
    decAux acc (s.flatMap (fun b => [true, b]) ++ [false] ++ rest) =
      (acc.reverse ++ s) :: decAux [] rest := by
  induction s generalizing acc with
  | nil => simp [decAux]
  | cons b s ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    rw [decAux, ih]
    simp

/-- `decList` is a left inverse of `encList`. -/
@[simp] lemma decList_encList (L : List (List Bool)) : decList (encList L) = L := by
  induction L with
  | nil => rfl
  | cons s L ih =>
    simp only [decList, encList, List.flatMap_cons, encStr] at ih ⊢
    rw [decAux_encStr_append, ih]
    simp

/-- A string `s` is encoded with `2 |s| + 1` bits. -/
lemma length_encStr (s : List Bool) : (encStr s).length = 2 * s.length + 1 := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    simp only [encStr, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

/-- The length of the encoding of a tuple of strings is `Σ (2|sᵢ| + 1)`. -/
lemma length_encList (L : List (List Bool)) :
    (encList L).length = (L.map fun s => 2 * s.length + 1).sum := by
  induction L with
  | nil => rfl
  | cons s L ih =>
    simp only [encList, List.flatMap_cons, List.length_append, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [length_encStr, ih]

/-- A tuple of `k` strings of length `≤ p` is encoded with at most `k (2p + 1)` bits. -/
lemma length_encList_le (L : List (List Bool)) (p : ℕ) (h : ∀ s ∈ L, s.length ≤ p) :
    (encList L).length ≤ L.length * (2 * p + 1) := by
  induction L with
  | nil => simp [encList]
  | cons s L ih =>
    simp only [encList, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    rw [length_encStr]
    have h1 := h s (by simp)
    have h2 := ih (fun s hs => h s (by simp [hs]))
    nlinarith

section Chunk

variable {α : Type*}

/-- The `i`-th block of length `L` of `S`. -/
def chunk (S : List α) (L i : ℕ) : List α := (S.drop (i * L)).take L

/-- Blocks have length at most `L`. -/
lemma length_chunk_le (S : List α) (L i : ℕ) : (chunk S L i).length ≤ L := by
  simp [chunk]

/-- The first `k` blocks of length `L` concatenate to the prefix of length `k L`. -/
lemma flatten_chunks_take (S : List α) (L k : ℕ) :
    ((List.range k).map (chunk S L)).flatten = S.take (k * L) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      chunk]
    rw [Nat.succ_mul, List.take_add]

/-- The `k` blocks of length `⌈|S|/k⌉` concatenate to `S`. -/
lemma flatten_chunks (S : List α) {k : ℕ} (hk : 0 < k) :
    ((List.range k).map (chunk S (S.length ⌈/⌉ k))).flatten = S := by
  rw [flatten_chunks_take, List.take_of_length_le (Nat.le_mul_ceilDiv hk)]

end Chunk

end Cslib.BitEncoding

namespace List

/-- For a duplicate-free list `l`, mapping `u ↦ f (index of u in l)` over `l` is mapping `f` over
the indices. -/
theorem Nodup.map_idxOf {α β : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup) (f : ℕ → β) :
    l.map (fun u => f (l.idxOf u)) = (List.range l.length).map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  congr 1
  exact hl.idxOf_getElem i (by simpa using h1)

end List
