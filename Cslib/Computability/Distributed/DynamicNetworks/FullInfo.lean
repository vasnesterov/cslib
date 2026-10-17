/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.DynamicNetworks.HeardOf
public import Cslib.Computability.Distributed.DynamicNetworks.Journey

/-!
# Full-information indistinguishability in dynamic networks

Synchronous rounds; in round `t + 1` the adversary chooses a communication graph `E t`
(`Cslib.HeardOf.Graph` convention: `E t q p` means that `p` receives `q`'s message). In a
full-information protocol the local state of `p` after `t` rounds is its *view*: its initial
state, and, for every round, the set of processes it heard from and their views. Rather than
building a view type, we define "same view in two executions" directly by recursion on `t`:

* `FIIndist I E F t p`: process `p` has the same view after `t` rounds in an execution with
  communication pattern `E` and in one with pattern `F`, where `I q` says that `q` starts with the
  same initial view in both (same input, same identifier, same a-priori information, …).

This is the indistinguishability relation of Kuhn–Moses–Oshman (PODC'11), Nowak–Schmid–Winkler
(PODC'19) and of Heard-Of style lower bounds. `conf_eq_of_fiIndist` shows that it is the coarsest
relation needed: the state of *every* deterministic full-information algorithm (`HeardOf.conf`)
is a function of the view.

We also define one structure for full-information algorithms with inputs and outputs
(`HeardOf.Algorithm`: initial states, transition function, output map).

## Main results

* `FIIndist.symm`, `FIIndist.trans`, `FIIndist.refl_of`, `FIIndist.mono`, `FIIndist.imp`.
* `FIIndist.journey`: the view determines the causal past (journeys into `p`) and the views of
  all time-nodes in it.
* `FIIndist.of_agree` (**locality**): executions that agree on the initial views of the causal
  past of `(p, t)` and on the edges into it are indistinguishable for `p` at time `t`.
* `fiIndist_congr`: the view after `t` rounds only depends on the first `t` graphs.
* `conf_eq_of_fiIndist` (the bridge to CSLib `HeardOf.conf`).
-/

@[expose] public section

namespace Cslib.HeardOf

open Cslib.DynNet

variable {α σ : Type*}

/-- `FIIndist I E F t p`: process `p` has the same full-information view after `t` rounds of the
patterns `E` and `F` (`E t q p`: `p` receives `q` in round `t + 1`), where `I q` means that `q`
has the same initial view in both executions. -/
def FIIndist (I : α → Prop) (E F : ℕ → Graph α) : ℕ → α → Prop
  | 0, p => I p
  | t + 1, p => FIIndist I E F t p ∧ (∀ q, E t q p ↔ F t q p) ∧ ∀ q, E t q p → FIIndist I E F t q

variable {I I' : α → Prop} {E F G : ℕ → Graph α}

namespace FIIndist

/-- The view at time `0` is the initial view. -/
theorem zero_iff {p : α} : FIIndist I E F 0 p ↔ I p := Iff.rfl

/-- The recursive step of the view: previous view, same in-neighbours, their previous views. -/
theorem succ_iff {t : ℕ} {p : α} : FIIndist I E F (t + 1) p ↔ FIIndist I E F t p ∧
    (∀ q, E t q p ↔ F t q p) ∧ ∀ q, E t q p → FIIndist I E F t q := Iff.rfl

/-- Same view now implies same view one round earlier. -/
theorem pred {t : ℕ} {p : α} (h : FIIndist I E F (t + 1) p) : FIIndist I E F t p := h.1

/-- Same view now implies same view at all earlier times. -/
theorem mono {t t' : ℕ} {p : α} (h : FIIndist I E F t' p) (htt : t ≤ t') : FIIndist I E F t p := by
  induction t' with
  | zero => obtain rfl : t = 0 := by omega
            exact h
  | succ t' ih =>
    rcases Nat.eq_or_lt_of_le htt with rfl | hlt
    · exact h
    · exact ih h.pred (by omega)

/-- Processes with the same view have the same initial view. -/
theorem zero {t : ℕ} {p : α} (h : FIIndist I E F t p) : I p := h.mono (Nat.zero_le _)

/-- Weaken the initial-view relation. -/
theorem imp (hI : ∀ p, I p → I' p) {t : ℕ} {p : α} (h : FIIndist I E F t p) :
    FIIndist I' E F t p := by
  induction t generalizing p with
  | zero => exact hI p h
  | succ t ih => exact ⟨ih h.1, h.2.1, fun q hq => ih (h.2.2 q hq)⟩

/-- Symmetry, given symmetry of the initial-view relation. -/
theorem symm (hI : ∀ p, I p → I' p) {t : ℕ} {p : α} (h : FIIndist I E F t p) :
    FIIndist I' F E t p := by
  induction t generalizing p with
  | zero => exact hI p h
  | succ t ih =>
    exact ⟨ih h.1, fun q => (h.2.1 q).symm, fun q hq => ih (h.2.2 q ((h.2.1 q).2 hq))⟩

/-- Transitivity, given transitivity of the initial-view relations. -/
theorem trans {I₁ I₂ I₃ : α → Prop} (hI : ∀ p, I₁ p → I₂ p → I₃ p) {t : ℕ} {p : α}
    (h₁ : FIIndist I₁ E F t p) (h₂ : FIIndist I₂ F G t p) : FIIndist I₃ E G t p := by
  induction t generalizing p with
  | zero => exact hI p h₁ h₂
  | succ t ih =>
    exact ⟨ih h₁.1 h₂.1, fun q => (h₁.2.1 q).trans (h₂.2.1 q),
      fun q hq => ih (h₁.2.2 q hq) (h₂.2.2 q ((h₁.2.1 q).1 hq))⟩

/-- Reflexivity on a set of processes that is closed under in-neighbours and whose initial views
agree. -/
theorem refl_of {S : Set α} (hI : ∀ p ∈ S, I p) (hS : ∀ t, ∀ p ∈ S, ∀ q, E t q p → q ∈ S) :
    ∀ t, ∀ p ∈ S, FIIndist I E E t p
  | 0, p, hp => hI p hp
  | t + 1, p, hp => ⟨refl_of hI hS t p hp, fun _ => Iff.rfl,
      fun q hq => refl_of hI hS t q (hS t p hp q hq)⟩

/-- Reflexivity when all initial views agree. -/
theorem refl (hI : ∀ p, I p) (t : ℕ) (p : α) : FIIndist I E E t p :=
  refl_of (S := Set.univ) (fun p _ => hI p) (fun _ _ _ _ _ => trivial) t p trivial

/-- A process that receives nothing in a round keeps its view. -/
theorem succ_of_deaf {t : ℕ} {p : α} (h : FIIndist I E F t p) (hE : ∀ q, ¬ E t q p)
    (hF : ∀ q, ¬ F t q p) : FIIndist I E F (t + 1) p :=
  ⟨h, fun q => ⟨fun h' => (hE q h').elim, fun h' => (hF q h').elim⟩, fun q h' => (hE q h').elim⟩

/-- **The view determines the causal past**, and the views of all time-nodes in it. -/
theorem journey {s t : ℕ} {p q : α} (h : FIIndist I E F t p) (hr : Journey E s q t p) :
    Journey F s q t p ∧ FIIndist I E F s q := by
  induction hr with
  | refl => exact ⟨.refl, h⟩
  | @step w u t _ hwu ih =>
    rcases hwu with rfl | hwu
    · obtain ⟨h1, h2⟩ := ih h.pred
      exact ⟨h1.stay, h2⟩
    · obtain ⟨h1, h2⟩ := ih (h.2.2 w hwu)
      exact ⟨.step h1 (Or.inr ((h.2.1 w).1 hwu)), h2⟩

/-- **Locality.** If two executions agree on the initial views of the time-`0` nodes in the causal
past of `(p, t)` and on the edges into all time-nodes of that causal past, then `p` cannot
distinguish them at time `t`. -/
theorem of_agree {t : ℕ} {p : α} (hI : ∀ q, Journey E 0 q t p → I q)
    (hE : ∀ q s, Journey E (s + 1) q t p → ∀ w, E s w q ↔ F s w q) : FIIndist I E F t p := by
  induction t generalizing p with
  | zero => exact hI p .refl
  | succ t ih =>
    refine ⟨ih (fun q hq => hI q hq.stay) (fun q s hq => hE q s hq.stay), hE p t .refl,
      fun q hq => ?_⟩
    exact ih (fun w hw => hI w (.step hw (Or.inr hq)))
      (fun w s hw => hE w s (.step hw (Or.inr hq)))

end FIIndist

/-- The view after `t` rounds only depends on the first `t` graphs. -/
theorem fiIndist_congr {E' F' : ℕ → Graph α} :
    ∀ {t : ℕ}, (∀ k < t, E k = E' k) → (∀ k < t, F k = F' k) → ∀ p,
      FIIndist I E F t p ↔ FIIndist I E' F' t p
  | 0, _, _, _ => Iff.rfl
  | t + 1, hE, hF, p => by
    have ih := fiIndist_congr (t := t) (fun k hk => hE k (Nat.lt_succ_of_lt hk))
      (fun k hk => hF k (Nat.lt_succ_of_lt hk))
    simp only [FIIndist, ih, hE t (Nat.lt_succ_self t), hF t (Nat.lt_succ_self t)]

/-- **The state of every full-information algorithm is a function of the view.** -/
theorem conf_eq_of_fiIndist {step : StepFn α σ} {C C' : α → σ} (hI : ∀ p, I p → C p = C' p)
    {t : ℕ} {p : α} (h : FIIndist I E F t p) : conf step C E t p = conf step C' F t p := by
  induction t generalizing p with
  | zero => exact hI p h
  | succ t ih =>
    refine next_eq_of_agree (fun q => ?_) (fun q hq => ?_)
    · simp only [Hears, h.2.1 q]
    · rcases hq with rfl | hq
      · exact ih h.1
      · exact ih (h.2.2 q hq)

/-! ### Full-information algorithms with inputs and outputs -/

/-- A deterministic full-information algorithm with inputs in `V` and outputs in `O`: `init i v`
is the initial state of agent `i` with input `v`, `step` the transition function, `out s` the
output (decision / output variable) in state `s`. -/
structure Algorithm (α σ V O : Type*) where
  /-- The initial state of an agent, from its identity and input. -/
  init : α → V → σ
  /-- The transition function. -/
  step : StepFn α σ
  /-- The output of a state. -/
  out : σ → O

namespace Algorithm

variable {V O : Type*} (A : Algorithm α σ V O)

/-- The initial configuration with inputs `x`. -/
def initC (x : α → V) : α → σ := fun i => A.init i (x i)

/-- The initial state of `i` from inputs `x`. -/
@[simp] theorem initC_apply (x : α → V) (i : α) : A.initC x i = A.init i (x i) := rfl

end Algorithm

end Cslib.HeardOf
