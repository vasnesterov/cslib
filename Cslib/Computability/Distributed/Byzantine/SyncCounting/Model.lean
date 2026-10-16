/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.NormNum.Ineq

/-!
# Synchronous counting: the self-stabilising Byzantine state-broadcast model

The model of Lenzen, Rybicki and Suomela [LenzenRybickiSuomela2015] (§2), also used by Dolev et al.,
*Synchronous counting and computational algorithm design*, and later papers on synchronous
counting and firing squads.

* A complete network of nodes `V` runs in synchronous lock-step rounds.
* A deterministic algorithm `A = (X, g, h)`: in every round every node broadcasts its whole
  state; node `i` receiving the vector `m : V → X` moves to the state `g i m`; its output is
  `h i s ∈ Fin c`.
* **Arbitrary initial states** (self-stabilisation): an execution is any sequence of global states
  `x : ℕ → V → X` (no constraint on `x 0`).
* A static set `F` of **Byzantine** nodes: they may send arbitrary, different states to different
  nodes. Formally, `x (t+1) i = g i m` for some vector `m` that agrees with `x t` on the correct
  nodes (`IsExec`). The states `x t j` of faulty `j` are meaningless.
* `StabilisesIn A F x T`: from round `T` on, all correct nodes output the same value and increment
  it by one modulo `c` every round. `IsCounter A f T`: every execution with at most `f` faulty nodes
  stabilises within `T` rounds ("`A ∈ 𝒜(n, f, c)` with `T(A) ≤ T`").
* `Achievable n f c T S`: there is a synchronous `c`-counter on `n` nodes with resilience `f`,
  stabilisation time `≤ T` and a nonempty finite state space of at most `2 ^ S` states, i.e. with
  `S(A) = ⌈log₂ |X|⌉ ≤ S` state bits.

Nonemptiness of `X` matters: with `X = ∅` there are no executions and every algorithm would be a
counter vacuously.

## Related models in CSLib

`Cslib.Byzantine.LockStep` is a general synchronous Byzantine model with history-based protocols
and a fixed initial state. This model is the special case needed for self-stabilisation: the
complete network, full-state broadcast, memoryless transitions and *arbitrary* initial states.
It is kept separate because executions from arbitrary states are not runs of a history-based
protocol.

## References

* [C. Lenzen, J. Rybicki, J. Suomela, *Towards optimal synchronous
  counting*][LenzenRybickiSuomela2015]
-/

@[expose] public section

namespace Cslib.Byzantine.SyncCounting

/-- A deterministic synchronous algorithm `(X, g, h)` on the node set `V` with states `X` and
outputs in `Fin c`. -/
structure Algorithm (V X : Type*) (c : ℕ) where
  /-- State transition: node `i` receiving the state vector `m` moves to `g i m`. -/
  g : V → (V → X) → X
  /-- Output function. -/
  h : V → X → Fin c

variable {V X : Type*} {c : ℕ}

/-- `x` is an execution of `A` with faulty set `F` (from an arbitrary initial state): every correct
node's next state is its transition applied to *some* received vector that agrees with the current
states on the correct nodes (the Byzantine entries are arbitrary and may differ between
receivers). -/
def IsExec (A : Algorithm V X c) (F : Finset V) (x : ℕ → V → X) : Prop :=
  ∀ t, ∀ i ∉ F, ∃ m : V → X, (∀ j ∉ F, m j = x t j) ∧ x (t + 1) i = A.g i m

/-- The execution `x` stabilises within `T` rounds: there is `v` such that every correct node `i`
outputs `(v + r) mod c` in round `T + r`, for all `r`. -/
def StabilisesIn (A : Algorithm V X c) (F : Finset V) (x : ℕ → V → X) (T : ℕ) : Prop :=
  ∃ v : ℕ, ∀ r, ∀ i ∉ F, ((A.h i (x (T + r) i) : Fin c) : ℕ) = (v + r) % c

/-- `A` is a synchronous `c`-counter with resilience `f` and stabilisation time at most `T`. -/
def IsCounter (A : Algorithm V X c) (f T : ℕ) : Prop :=
  ∀ F : Finset V, F.card ≤ f → ∀ x, IsExec A F x → StabilisesIn A F x T

/-- There is a synchronous `c`-counter on `n` nodes with resilience `f`, stabilisation time at most
`T` and at most `S` bits of state (a nonempty state set with `≤ 2 ^ S` elements). -/
def Achievable (n f c T S : ℕ) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (_ : Nonempty X) (A : Algorithm (Fin n) X c),
    Fintype.card X ≤ 2 ^ S ∧ IsCounter A f T

/-! ### Basic lemmas -/

lemma StabilisesIn.mono {A : Algorithm V X c} {F : Finset V} {x : ℕ → V → X} {T T' : ℕ}
    (h : StabilisesIn A F x T) (hT : T ≤ T') : StabilisesIn A F x T' := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v + (T' - T), fun r i hi => ?_⟩
  have := hv (T' - T + r) i hi
  rw [show T + (T' - T + r) = T' + r by omega] at this
  rw [this]; congr 1; omega

lemma IsCounter.mono {A : Algorithm V X c} {f T T' : ℕ} (h : IsCounter A f T) (hT : T ≤ T') :
    IsCounter A f T' := fun F hF x hx => (h F hF x hx).mono hT

lemma IsCounter.anti {A : Algorithm V X c} {f f' T : ℕ} (h : IsCounter A f T) (hf : f' ≤ f) :
    IsCounter A f' T := fun F hF x hx => h F (hF.trans hf) x hx

lemma Achievable.mono {n f c T S T' S' : ℕ} (h : Achievable n f c T S) (hT : T ≤ T')
    (hS : S ≤ S') : Achievable n f c T' S' := by
  obtain ⟨X, _, _, A, hX, hA⟩ := h
  exact ⟨X, _, ‹_›, A, hX.trans (Nat.pow_le_pow_right (by norm_num) hS), hA.mono hT⟩

/-- In a stabilised execution all correct nodes have the same output in every round from `T` on. -/
lemma StabilisesIn.out_eq {A : Algorithm V X c} {F : Finset V} {x : ℕ → V → X} {T : ℕ}
    (h : StabilisesIn A F x T) {t : ℕ} (ht : T ≤ t) {i j : V} (hi : i ∉ F) (hj : j ∉ F) :
    A.h i (x t i) = A.h j (x t j) := by
  obtain ⟨v, hv⟩ := h
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact Fin.ext ((hv r i hi).trans (hv r j hj).symm)

/-- The fault-free execution from the initial state `x₀`. -/
def run (A : Algorithm V X c) (x₀ : V → X) : ℕ → V → X
  | 0 => x₀
  | t + 1 => fun i => A.g i (run A x₀ t)

lemma isExec_run (A : Algorithm V X c) (x₀ : V → X) (F : Finset V) : IsExec A F (run A x₀) :=
  fun t _ _ => ⟨run A x₀ t, fun _ _ => rfl, rfl⟩

/-! ### Relabelling the nodes -/

/-- Transport an algorithm along a bijection of the node sets. -/
def Algorithm.reindex {W : Type*} (A : Algorithm V X c) (e : V ≃ W) : Algorithm W X c where
  g w m := A.g (e.symm w) (fun v => m (e v))
  h w s := A.h (e.symm w) s

lemma IsCounter.reindex {W : Type*} {A : Algorithm V X c} {f T : ℕ} (hA : IsCounter A f T)
    (e : V ≃ W) : IsCounter (A.reindex e) f T := by
  classical
  intro F hF x hx
  have hF' : (F.map e.symm.toEmbedding).card ≤ f := by simpa using hF
  have hmem : ∀ v, v ∉ F.map e.symm.toEmbedding ↔ e v ∉ F := by
    intro v; simp [Finset.mem_map_equiv]
  have hx' : IsExec A (F.map e.symm.toEmbedding) (fun t v => x t (e v)) := by
    intro t v hv
    obtain ⟨m, hm, hstep⟩ := hx t (e v) ((hmem v).1 hv)
    refine ⟨fun u => m (e u), fun u hu => hm _ ((hmem u).1 hu), ?_⟩
    simp only [hstep, Algorithm.reindex, Equiv.symm_apply_apply]
  obtain ⟨v, hv⟩ := hA _ hF' _ hx'
  refine ⟨v, fun r w hw => ?_⟩
  have := hv r (e.symm w) (by rw [hmem]; simpa using hw)
  simpa [Algorithm.reindex] using this

/-- Achievability only depends on the number of nodes. -/
lemma achievable_of_equiv {W : Type*} [Fintype W] {f c T S : ℕ} {X : Type} [Fintype X]
    [Nonempty X] (A : Algorithm W X c) (hX : Fintype.card X ≤ 2 ^ S) (hA : IsCounter A f T) :
    Achievable (Fintype.card W) f c T S :=
  ⟨X, _, ‹_›, A.reindex (Fintype.equivFin W), hX, hA.reindex _⟩

end Cslib.Byzantine.SyncCounting
