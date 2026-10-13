/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Set.Insert

/-!
# Round-based full-information dynamic networks (Heard-Of style)

A set of agents `α` communicates in synchronous, communication-closed rounds. In each round the
adversary picks a directed communication graph `G : Graph α` (`G j i`: `i` receives `j`'s
message; self-loops are implicit, every agent always "hears" itself). Every agent broadcasts its
full local state and then applies a deterministic transition function to the vector of received
states (`none` for agents it did not hear). This is the full-information Heard-Of model of
Charron-Bost–Schiper, as used e.g. by Függer–Nowak–Schwarz (PODC 2018). It complements the
relational view of dynamic networks in `Cslib.DynNet` (products of communication graphs): here the
states of the agents are tracked explicitly, which is what indistinguishability arguments need.

## Main definitions

* `Hears G i j`, `Deaf G i`, `SameIn G H i` (same in-neighbourhood of `i`).
* `next step G C`, `conf step C p t`: one round, and the configuration after `t` rounds of the
  communication pattern `p : ℕ → Graph α` (`p t` is the graph of round `t + 1`).
* `Pat N`: communication patterns in a network model `N : Set (Graph α)`.
* `pcons`, `splice`, `shift`: operations on patterns.

## Main results

* `next_eq_of_agree` (Lemma 6 of Függer–Nowak–Schwarz: indistinguishability is preserved).
* `conf_agree`: a set of agents that only hears itself keeps its states.
* `conf_add`, `conf_splice`, `conf_pcons_succ`.

## References

* [B. Charron-Bost, A. Schiper, *The Heard-Of model: computing in distributed systems with benign
  faults*][CharronBostSchiper2009]
* [M. Függer, T. Nowak, M. Schwarz, *Tight Bounds for Asymptotic and Approximate
  Consensus*][FuggerNowakSchwarz2018]
-/

@[expose] public section

namespace Cslib.HeardOf

variable {α σ : Type*}

/-- A communication graph: `G j i` means that agent `i` receives the message of agent `j`.
Self-loops are implicit (see `Hears`). -/
abbrev Graph (α : Type*) := α → α → Prop

/-- `i` hears `j` in `G` (every agent hears itself). -/
def Hears (G : Graph α) (i j : α) : Prop := j = i ∨ G j i

/-- `i` is deaf in `G`: its only in-neighbour is itself. -/
def Deaf (G : Graph α) (i : α) : Prop := ∀ j, G j i → j = i

/-- `i` has the same in-neighbours in `G` and `H`. -/
def SameIn (G H : Graph α) (i : α) : Prop := ∀ j, Hears G i j ↔ Hears H i j

theorem hears_self (G : Graph α) (i : α) : Hears G i i := Or.inl rfl

theorem Deaf.eq {G : Graph α} {i j : α} (h : Deaf G i) (hj : Hears G i j) : j = i :=
  hj.elim id (h j)

theorem SameIn.refl (G : Graph α) (i : α) : SameIn G G i := fun _ => Iff.rfl

theorem SameIn.symm {G H : Graph α} {i : α} (h : SameIn G H i) : SameIn H G i :=
  fun j => (h j).symm

/-- A transition function: agent `i` maps the received states (`none` = not heard) to its new
state. Its own state is always received (`msgs i = some (C i)`). -/
abbrev StepFn (α σ : Type*) := α → (α → Option σ) → σ

open Classical in
/-- The messages received by `i` in graph `G` from configuration `C`. -/
noncomputable def msgs (G : Graph α) (C : α → σ) (i : α) : α → Option σ :=
  fun j => if Hears G i j then some (C j) else none

/-- One round: the successor configuration `G.C`. -/
noncomputable def next (step : StepFn α σ) (G : Graph α) (C : α → σ) : α → σ :=
  fun i => step i (msgs G C i)

/-- The configuration after `t` rounds of pattern `p` from `C` (`p t` = graph of round `t+1`). -/
noncomputable def conf (step : StepFn α σ) (C : α → σ) (p : ℕ → Graph α) : ℕ → α → σ
  | 0 => C
  | t + 1 => next step (p t) (conf step C p t)

/-- Communication patterns of a network model `N`. -/
def Pat (N : Set (Graph α)) : Set (ℕ → Graph α) := {p | ∀ t, p t ∈ N}

/-- Prepend a graph to a pattern. -/
def pcons (G : Graph α) (q : ℕ → Graph α) : ℕ → Graph α
  | 0 => G
  | k + 1 => q k

/-- Drop the first `t` rounds. -/
def shift (t : ℕ) (p : ℕ → Graph α) : ℕ → Graph α := fun k => p (t + k)

/-- First `t` rounds of `p`, then `q`. -/
def splice (p : ℕ → Graph α) (t : ℕ) (q : ℕ → Graph α) : ℕ → Graph α :=
  fun k => if k < t then p k else q (k - t)

variable {step : StepFn α σ}

@[simp] theorem conf_zero (C : α → σ) (p : ℕ → Graph α) : conf step C p 0 = C := rfl

theorem conf_succ (C : α → σ) (p : ℕ → Graph α) (t : ℕ) :
    conf step C p (t + 1) = next step (p t) (conf step C p t) := rfl

theorem conf_add (C : α → σ) (p : ℕ → Graph α) (t s : ℕ) :
    conf step C p (t + s) = conf step (conf step C p t) (shift t p) s := by
  induction s with
  | zero => rfl
  | succ s ih => rw [← Nat.add_assoc, conf_succ, ih]; rfl

theorem conf_congr (C : α → σ) {p q : ℕ → Graph α} {t : ℕ} (h : ∀ k < t, p k = q k) :
    conf step C p t = conf step C q t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [conf_succ, conf_succ, ih (fun k hk => h k (by omega)), h t (by omega)]

theorem conf_pcons_succ (C : α → σ) (G : Graph α) (q : ℕ → Graph α) (s : ℕ) :
    conf step C (pcons G q) (s + 1) = conf step (next step G C) q s := by
  rw [Nat.add_comm, conf_add]
  have : shift 1 (pcons G q) = q := by funext k; rw [shift, Nat.add_comm]; rfl
  rw [this]; rfl

theorem conf_splice_le (C : α → σ) (p q : ℕ → Graph α) {t s : ℕ} (hs : s ≤ t) :
    conf step C (splice p t q) s = conf step C p s :=
  conf_congr C (fun k hk => by simp [splice, show k < t by omega])

theorem conf_splice (C : α → σ) (p q : ℕ → Graph α) (t s : ℕ) :
    conf step C (splice p t q) (t + s) = conf step (conf step C p t) q s := by
  rw [conf_add, conf_splice_le C p q le_rfl]
  congr 1
  funext k; simp [shift, splice]

theorem shift_mem_pat {N : Set (Graph α)} {p : ℕ → Graph α} (hp : p ∈ Pat N) (t : ℕ) :
    shift t p ∈ Pat N := fun k => hp (t + k)

theorem pcons_mem_pat {N : Set (Graph α)} {G : Graph α} {q : ℕ → Graph α} (hG : G ∈ N)
    (hq : q ∈ Pat N) : pcons G q ∈ Pat N := by
  intro k; cases k with
  | zero => exact hG
  | succ k => exact hq k

theorem splice_mem_pat {N : Set (Graph α)} {p q : ℕ → Graph α} (hp : p ∈ Pat N)
    (hq : q ∈ Pat N) (t : ℕ) : splice p t q ∈ Pat N := by
  intro k; unfold splice; split_ifs
  · exact hp k
  · exact hq _

theorem const_mem_pat {N : Set (Graph α)} {G : Graph α} (hG : G ∈ N) :
    (fun _ => G) ∈ Pat N := fun _ => hG

theorem pat_mono {N N' : Set (Graph α)} (h : N' ⊆ N) : Pat N' ⊆ Pat N :=
  fun _ hp t => h (hp t)

/-- **Lemma 6 of Függer–Nowak–Schwarz.** If `i` has the same in-neighbours in `G` and `H` and
all of them are in the same state in `C` and `C'`, then `i` is in the same state in `G.C` and
`H.C'`. -/
theorem next_eq_of_agree {G H : Graph α} {C C' : α → σ} {i : α} (hin : SameIn G H i)
    (hC : ∀ j, Hears G i j → C j = C' j) : next step G C i = next step H C' i := by
  unfold next
  congr 1
  funext j
  unfold msgs
  by_cases h : Hears G i j
  · simp [h, (hin j).1 h, hC j h]
  · have h' : ¬ Hears H i j := fun h' => h ((hin j).2 h')
    simp [h, h']

/-- Indistinguishability along runs: if the agents of `S` have the same in-neighbourhoods in
`p t` and `p' t`, only hear agents of `S`, and start in the same states, they stay in the same
states forever. -/
theorem conf_agree (S : Set α) {C C' : α → σ} {p p' : ℕ → Graph α}
    (hsame : ∀ t, ∀ i ∈ S, SameIn (p t) (p' t) i)
    (hclosed : ∀ t, ∀ i ∈ S, ∀ j, Hears (p t) i j → j ∈ S)
    (hC : ∀ i ∈ S, C i = C' i) : ∀ t, ∀ i ∈ S, conf step C p t i = conf step C' p' t i := by
  intro t
  induction t with
  | zero => exact hC
  | succ t ih =>
    intro i hi
    exact next_eq_of_agree (hsame t i hi) (fun j hj => ih j (hclosed t i hi j hj))

/-- A deaf agent's trajectory only depends on its own state. -/
theorem conf_agree_deaf {C C' : α → σ} {p p' : ℕ → Graph α} {i : α}
    (hp : ∀ t, Deaf (p t) i) (hp' : ∀ t, Deaf (p' t) i) (hC : C i = C' i) (t : ℕ) :
    conf step C p t i = conf step C' p' t i := by
  refine conf_agree {i} (fun t k hk j => ?_) (fun t k hk j hj => ?_) (fun k hk => ?_) t i rfl
  · rw [Set.mem_singleton_iff] at hk; subst hk
    constructor
    · intro h; exact Or.inl ((hp t).eq h)
    · intro h; exact Or.inl ((hp' t).eq h)
  · rw [Set.mem_singleton_iff] at hk ⊢; subst hk; exact (hp t).eq hj
  · rw [Set.mem_singleton_iff] at hk; subst hk; exact hC

end Cslib.HeardOf
