/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.CommunicationComplexity.Protocol
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Ring

/-!
# Deterministic CONGEST algorithms and lower bounds from two-party communication complexity


* `Algorithm V I σ B`: a deterministic synchronous message-passing algorithm on the vertex set `V`
  (vertex names are the IDs and are known to the algorithm), with node inputs in `I`, local states
  in `σ`, and messages of exactly `B` bits per edge, direction and round (CONGEST with bandwidth
  `B`; "no message" can be encoded with one extra bit). `Algorithm.run` is the synchronous
  execution on a graph `G`, `Algorithm.Accepts` means that all nodes accept after `T` rounds.
* `LBFamily X Y V I`: a **family of lower bound graphs** (Definition 1.1 of Bachrach et al.,
  PODC'19, taken from Censor-Hillel–Khoury–Paz, DISC'17): graphs `G x y` on a fixed vertex set
  with a fixed partition `V = V_A ∪ V_B`, where the part inside `V_A` (edges and node inputs)
  depends only on `x`, the part inside `V_B` only on `y`, and the cut edges are fixed and contained
  in the finset `Ecut`.
* `LBFamily.simulation`: Alice and Bob simulate a `T`-round algorithm with
  `T · 2 · |Ecut| · B + 2` bits (Theorem 1.1, the simulation half).
* `LBFamily.lowerBound`, `LBFamily.disj_lowerBound`: Theorem 1.1 (deterministic): if every
  protocol for `f` needs `C` bits and an algorithm decides, within `T` rounds, a predicate that is
  equivalent to `f` on the family, then `C ≤ T · 2 · |Ecut| · B + 2`. For `f = DISJ_K` this is
  unconditional (`K ≤ T · 2 · |Ecut| · B + 2`), by the fooling-set bound.
-/

@[expose] public section

namespace Cslib.Congest

open Cslib.CommunicationComplexity

/-- `B`-bit messages. -/
abbrev Msg (B : ℕ) := Fin B → Bool

/-- A deterministic synchronous CONGEST algorithm with `B`-bit messages. In every round each node
`v` sends `send v s w` to every neighbour `w` (`s` = current state of `v`), then updates its state
with `step`, receiving `some m` from each neighbour and `none` from non-neighbours. -/
structure Algorithm (V I σ : Type*) (B : ℕ) where
  /-- Initial state from the node's ID and input. -/
  init : V → I → σ
  /-- Message sent by `v` in state `s` to neighbour `w`. -/
  send : V → σ → V → Msg B
  /-- State update from the received messages. -/
  step : V → σ → (V → Option (Msg B)) → σ
  /-- Local output (accept / reject). -/
  out : V → σ → Bool

namespace Algorithm

variable {V I σ : Type*} {B : ℕ}

/-- The state of every node after `t` synchronous rounds on graph `G` with node inputs `inp`. -/
def run (A : Algorithm V I σ B) (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → I) :
    ℕ → V → σ
  | 0 => fun v => A.init v (inp v)
  | t + 1 => fun v => A.step v (A.run G inp t v)
      (fun w => if G.Adj w v then some (A.send w (A.run G inp t w) v) else none)

/-- After `T` rounds, every node accepts. (An algorithm *decides* a predicate `P` in `T` rounds if
`Accepts … T ↔ P`; this is the weakest of the usual output conventions.) -/
def Accepts (A : Algorithm V I σ B) (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → I)
    (T : ℕ) : Prop :=
  ∀ v, A.out v (A.run G inp T v) = true

/-- Acceptance on a finite graph is decidable. -/
instance [Fintype V] (A : Algorithm V I σ B) (G : SimpleGraph V) [DecidableRel G.Adj]
    (inp : V → I) (T : ℕ) : Decidable (A.Accepts G inp T) := by
  unfold Accepts; infer_instance

end Algorithm

/-- A family of lower bound graphs (Definition 1.1), indexed by Alice's input `x : X` and Bob's
input `y : Y`, with node inputs in `I`. `alice v = true` iff `v ∈ V_A`. -/
structure LBFamily (X Y V I : Type*) where
  /-- The graph for inputs `x`, `y`. -/
  G : X → Y → SimpleGraph V
  /-- Node inputs (e.g. the list of incident edges, edge weights, …). -/
  inp : X → Y → V → I
  /-- The fixed partition: `alice v = true` iff `v ∈ V_A`. -/
  alice : V → Bool
  /-- A finset containing all cut edges `(a, b)`, `a ∈ V_A`, `b ∈ V_B`. -/
  Ecut : Finset (V × V)
  Ecut_sub : ∀ p ∈ Ecut, alice p.1 = true ∧ alice p.2 = false
  adj_cut : ∀ x y a b, alice a = true → alice b = false → (G x y).Adj a b → (a, b) ∈ Ecut
  /-- `G[V_A]` does not depend on `y`. -/
  adj_alice : ∀ x y y' a b, alice a = true → alice b = true → ((G x y).Adj a b ↔ (G x y').Adj a b)
  /-- `G[V_B]` does not depend on `x`. -/
  adj_bob : ∀ x x' y a b, alice a = false → alice b = false → ((G x y).Adj a b ↔ (G x' y).Adj a b)
  /-- The cut edges do not depend on the inputs. -/
  adj_fixed : ∀ x x' y y' a b, alice a = true → alice b = false →
    ((G x y).Adj a b ↔ (G x' y').Adj a b)
  /-- Inputs of `V_A`-nodes do not depend on `y`. -/
  inp_alice : ∀ x y y' v, alice v = true → inp x y v = inp x y' v
  /-- Inputs of `V_B`-nodes do not depend on `x`. -/
  inp_bob : ∀ x x' y v, alice v = false → inp x y v = inp x' y v

namespace LBFamily

open Protocol

variable {X Y V I σ : Type*} {B : ℕ} (F : LBFamily X Y V I)

/-- Adjacency between `u` and an Alice vertex `v` does not depend on `y`. -/
lemma adj_alice' {x y y' u v} (hv : F.alice v = true) :
    (F.G x y).Adj u v ↔ (F.G x y').Adj u v := by
  cases hu : F.alice u
  · rw [(F.G x y).adj_comm, (F.G x y').adj_comm]
    exact F.adj_fixed x x y y' v u hv hu
  · exact F.adj_alice x y y' u v hu hv

/-- Adjacency between `u` and a Bob vertex `v` does not depend on `x`. -/
lemma adj_bob' {x x' y u v} (hv : F.alice v = false) :
    (F.G x y).Adj u v ↔ (F.G x' y).Adj u v := by
  cases hu : F.alice u
  · exact F.adj_bob x x' y u v hu hv
  · exact F.adj_fixed x x' y y u v hu hv

variable [∀ x y, DecidableRel (F.G x y).Adj]

/-- Alice's simulation of the states (meaningful at `V_A`-nodes), given her input, a dummy input
`y₀` for Bob, and the messages `hB t a b` that crossed the cut from `b ∈ V_B` to `a ∈ V_A`. -/
def simA (A : Algorithm V I σ B) (x : X) (y₀ : Y) (hB : ℕ → V → V → Msg B) : ℕ → V → σ
  | 0 => fun v => A.init v (F.inp x y₀ v)
  | t + 1 => fun v => A.step v (simA A x y₀ hB t v)
      (fun w => if (F.G x y₀).Adj w v then
        some (if F.alice w then A.send w (simA A x y₀ hB t w) v else hB t v w) else none)

/-- Bob's simulation of the states (meaningful at `V_B`-nodes); `hA t a b` is the message from
`a ∈ V_A` to `b ∈ V_B` in round `t`. -/
def simB (A : Algorithm V I σ B) (x₀ : X) (y : Y) (hA : ℕ → V → V → Msg B) : ℕ → V → σ
  | 0 => fun v => A.init v (F.inp x₀ y v)
  | t + 1 => fun v => A.step v (simB A x₀ y hA t v)
      (fun w => if (F.G x₀ y).Adj w v then
        some (if F.alice w then hA t w v else A.send w (simB A x₀ y hA t w) v) else none)

/-- Alice's simulation is exact on `V_A`, given the correct messages from `V_B` in earlier rounds.
-/
lemma simA_eq (A : Algorithm V I σ B) (x : X) (y y₀ : Y) (hB : ℕ → V → V → Msg B) :
    ∀ t, (∀ s < t, ∀ a b, (a, b) ∈ F.Ecut →
        hB s a b = A.send b (A.run (F.G x y) (F.inp x y) s b) a) →
      ∀ v, F.alice v = true → F.simA A x y₀ hB t v = A.run (F.G x y) (F.inp x y) t v
  | 0, _, v, hv => by simp [simA, Algorithm.run, F.inp_alice x y₀ y v hv]
  | t + 1, h, v, hv => by
      have ih := simA_eq A x y y₀ hB t (fun s hs => h s (Nat.lt_succ_of_lt hs))
      simp only [simA, Algorithm.run]
      rw [ih v hv]
      congr 1
      funext w
      have hadj : (F.G x y₀).Adj w v ↔ (F.G x y).Adj w v := F.adj_alice' hv
      by_cases hwv : (F.G x y).Adj w v
      · simp only [hadj.2 hwv, hwv, ↓reduceIte, Option.some.injEq]
        cases hw : F.alice w
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact h t (Nat.lt_succ_self t) v w (F.adj_cut x y v w hv hw hwv.symm)
        · simp [ih w hw]
      · have h0 : ¬(F.G _ _).Adj w v := fun h' => hwv (hadj.1 h')
        simp only [h0, hwv, ↓reduceIte]

/-- Bob's simulation is exact on `V_B`, given the correct messages from `V_A` in earlier rounds. -/
lemma simB_eq (A : Algorithm V I σ B) (x x₀ : X) (y : Y) (hA : ℕ → V → V → Msg B) :
    ∀ t, (∀ s < t, ∀ a b, (a, b) ∈ F.Ecut →
        hA s a b = A.send a (A.run (F.G x y) (F.inp x y) s a) b) →
      ∀ v, F.alice v = false → F.simB A x₀ y hA t v = A.run (F.G x y) (F.inp x y) t v
  | 0, _, v, hv => by simp [simB, Algorithm.run, F.inp_bob x₀ x y v hv]
  | t + 1, h, v, hv => by
      have ih := simB_eq A x x₀ y hA t (fun s hs => h s (Nat.lt_succ_of_lt hs))
      simp only [simB, Algorithm.run]
      rw [ih v hv]
      congr 1
      funext w
      have hadj : (F.G x₀ y).Adj w v ↔ (F.G x y).Adj w v := F.adj_bob' hv
      by_cases hwv : (F.G x y).Adj w v
      · simp only [hadj.2 hwv, hwv, ↓reduceIte, Option.some.injEq]
        cases hw : F.alice w
        · simp [ih w hw]
        · simp only [↓reduceIte]
          exact h t (Nat.lt_succ_self t) w v (F.adj_cut x y w v hw hv hwv)
      · have h0 : ¬(F.G _ _).Adj w v := fun h' => hwv (hadj.1 h')
        simp only [h0, hwv, ↓reduceIte]

variable [DecidableEq V]

/-- Record the messages `m` of round `t` (indexed by the cut edges) in a message history. -/
def record (h : ℕ → V → V → Msg B) (t : ℕ) (m : F.Ecut → Msg B) : ℕ → V → V → Msg B :=
  fun s a b => if s = t then (if hab : (a, b) ∈ F.Ecut then m ⟨(a, b), hab⟩ else fun _ => false)
    else h s a b

/-- Alphabet size for one round of cut messages in one direction. -/
noncomputable abbrev roundAlphabet (B : ℕ) : ℕ := Fintype.card (F.Ecut → Msg B)

/-- The two-party protocol simulating the remaining `r` rounds, starting at round `t`, given the
message histories `hA` (Alice → Bob) and `hB` (Bob → Alice). In each round Alice sends all
messages of `V_A`-nodes on cut edges, then Bob sends those of `V_B`-nodes; at the end each player
sends one bit ("all my nodes accept"). -/
noncomputable def simProt [Fintype V] (A : Algorithm V I σ B) (x₀ : X) (y₀ : Y) :
    ℕ → ℕ → (ℕ → V → V → Msg B) → (ℕ → V → V → Msg B) → Protocol X Y Bool
  | 0, t, hA, hB =>
      .alice 2 (fun x => by
          classical exact if ∀ v, F.alice v = true → A.out v (F.simA A x y₀ hB t v) = true
            then 1 else 0)
        fun i => .bob 2 (fun y => by
            classical exact if ∀ v, F.alice v = false → A.out v (F.simB A x₀ y hA t v) = true
              then 1 else 0)
          fun j => .ret (decide (i = 1 ∧ j = 1))
  | r + 1, t, hA, hB =>
      .alice (F.roundAlphabet B)
        (fun x => Fintype.equivFin _
          (fun p : F.Ecut => A.send p.1.1 (F.simA A x y₀ hB t p.1.1) p.1.2))
        fun i => .bob (F.roundAlphabet B)
          (fun y => Fintype.equivFin _
            (fun p : F.Ecut => A.send p.1.2 (F.simB A x₀ y hA t p.1.2) p.1.1))
          fun j => simProt A x₀ y₀ r (t + 1)
            (F.record hA t ((Fintype.equivFin _).symm i))
            (F.record hB t ((Fintype.equivFin _).symm j))

omit [∀ x y, DecidableRel (F.G x y).Adj] in
/-- One round of cut messages in one direction costs `|Ecut| · B` bits. -/
lemma clog_roundAlphabet : Nat.clog 2 (F.roundAlphabet B) = F.Ecut.card * B := by
  simp only [roundAlphabet, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_coe]
  rw [← pow_mul, mul_comm B, Nat.clog_pow _ _ (by norm_num)]

/-- The simulating protocol for `r` rounds costs at most `r · 2 · |Ecut| · B + 2` bits. -/
lemma simProt_cost [Fintype V] (A : Algorithm V I σ B) (x₀ : X) (y₀ : Y) :
    ∀ r t hA hB, (F.simProt A x₀ y₀ r t hA hB).CostLE (r * (2 * (F.Ecut.card * B)) + 2)
  | 0, t, hA, hB => by
      have h2 : Nat.clog 2 2 = 1 := by simpa using Nat.clog_pow 2 1 (by norm_num)
      simp only [simProt, CostLE, zero_mul, zero_add, h2]
      exact ⟨by norm_num, fun i => ⟨by norm_num, fun j => trivial⟩⟩
  | r + 1, t, hA, hB => by
      simp only [simProt, CostLE, clog_roundAlphabet]
      set m := F.Ecut.card * B
      have e : (r + 1) * (2 * m) = r * (2 * m) + 2 * m := by ring
      refine ⟨by rw [e]; omega, fun i => ⟨by rw [e]; omega, fun j => ?_⟩⟩
      have : (r + 1) * (2 * m) + 2 - m - m = r * (2 * m) + 2 := by rw [e]; omega
      rw [this]
      exact simProt_cost A x₀ y₀ r (t + 1) _ _

/-- The simulating protocol computes "all nodes accept", given correct message histories. -/
lemma simProt_eval [Fintype V] (A : Algorithm V I σ B) (x₀ : X) (y₀ : Y)
    (x : X) (y : Y) :
    ∀ r t hA hB,
      (∀ s < t, ∀ a b, (a, b) ∈ F.Ecut → hA s a b = A.send a (A.run (F.G x y) (F.inp x y) s a) b) →
      (∀ s < t, ∀ a b, (a, b) ∈ F.Ecut → hB s a b = A.send b (A.run (F.G x y) (F.inp x y) s b) a) →
      (F.simProt A x₀ y₀ r t hA hB).eval x y =
        decide (A.Accepts (F.G x y) (F.inp x y) (t + r))
  | 0, t, hA, hB, hhA, hhB => by
      classical
      have eA := F.simA_eq A x y y₀ hB t hhB
      have eB := F.simB_eq A x x₀ y hA t hhA
      simp only [simProt, eval, add_zero, Algorithm.Accepts]
      have key : (∀ v, A.out v (A.run (F.G x y) (F.inp x y) t v) = true) ↔
          (∀ v, F.alice v = true → A.out v (F.simA A x y₀ hB t v) = true) ∧
            (∀ v, F.alice v = false → A.out v (F.simB A x₀ y hA t v) = true) := by
        constructor
        · intro h
          exact ⟨fun v hv => by rw [eA v hv]; exact h v, fun v hv => by rw [eB v hv]; exact h v⟩
        · rintro ⟨h1, h2⟩ v
          cases hv : F.alice v
          · rw [← eB v hv]; exact h2 v hv
          · rw [← eA v hv]; exact h1 v hv
      by_cases h1 : ∀ v, F.alice v = true → A.out v (F.simA A x y₀ hB t v) = true <;>
      by_cases h2 : ∀ v, F.alice v = false → A.out v (F.simB A x₀ y hA t v) = true <;>
      simp [h1, h2, key]
  | r + 1, t, hA, hB, hhA, hhB => by
      simp only [simProt, eval, Equiv.symm_apply_apply]
      rw [simProt_eval A x₀ y₀ x y r (t + 1), show t + 1 + r = t + (r + 1) by omega]
      · intro s hs a b hab
        simp only [record]
        split_ifs with hst
        · subst hst
          exact congrArg (fun st => A.send a st b)
            (F.simA_eq A x y y₀ hB s hhB a (F.Ecut_sub _ hab).1)
        · exact hhA s (by omega) a b hab
      · intro s hs a b hab
        simp only [record]
        split_ifs with hst
        · subst hst
          exact congrArg (fun st => A.send b st a)
            (F.simB_eq A x x₀ y hA s hhA b (F.Ecut_sub _ hab).2)
        · exact hhB s (by omega) a b hab

omit [DecidableEq V] in
/-- **Simulation** (Theorem 1.1 of Bachrach et al., communication part): a `T`-round CONGEST
algorithm with `B`-bit messages on a family of lower bound graphs yields a two-party protocol that
computes "all nodes accept" with at most `T · 2 · |Ecut| · B + 2` bits. -/
theorem simulation [Fintype V] [Nonempty X] [Nonempty Y]
    (A : Algorithm V I σ B) (T : ℕ) :
    ∃ P : Protocol X Y Bool, P.CostLE (T * (2 * (F.Ecut.card * B)) + 2) ∧
      P.Computes fun x y => decide (A.Accepts (F.G x y) (F.inp x y) T) := by
  classical
  refine ⟨F.simProt A (Classical.arbitrary X) (Classical.arbitrary Y) T 0
    (fun _ _ _ _ => false) (fun _ _ _ _ => false), F.simProt_cost A _ _ T 0 _ _, fun x y => ?_⟩
  rw [F.simProt_eval A _ _ x y T 0 _ _ (fun s hs => absurd hs (Nat.not_lt_zero s))
    (fun s hs => absurd hs (Nat.not_lt_zero s)), zero_add]

omit [DecidableEq V] in
/-- **Theorem 1.1 (deterministic).** If every protocol computing `f` needs at least `C` bits, and a
`T`-round algorithm with `B`-bit messages accepts `G x y` exactly when `f x y = true`, then
`C ≤ T · 2 · |Ecut| · B + 2`, i.e. `T ≥ (C - 2) / (2 |Ecut| B)`. -/
theorem lowerBound [Finite V] [Nonempty X] [Nonempty Y]
    (A : Algorithm V I σ B) (T : ℕ) (f : X → Y → Bool)
    (hA : ∀ x y, A.Accepts (F.G x y) (F.inp x y) T ↔ f x y = true) (C : ℕ)
    (hC : ∀ (P : Protocol X Y Bool) c, P.Computes f → P.CostLE c → C ≤ c) :
    C ≤ T * (2 * (F.Ecut.card * B)) + 2 := by
  have := Fintype.ofFinite V
  obtain ⟨P, hc, hP⟩ := F.simulation A T
  refine hC P _ (fun x y => ?_) hc
  rw [hP x y]
  cases h : f x y <;> simp [hA, h]

omit [DecidableEq V] in
/-- **Theorem 1.1 for set disjointness**, unconditional: if a `T`-round algorithm with `B`-bit
messages accepts `G x y` exactly when `DISJ_K(x, y) = TRUE`, then `K ≤ T · 2 · |Ecut| · B + 2`. -/
theorem disj_lowerBound {ι : Type*} [Fintype ι] [Finite V]
    (F : LBFamily (ι → Bool) (ι → Bool) V I) [∀ x y, DecidableRel (F.G x y).Adj]
    (A : Algorithm V I σ B) (T : ℕ)
    (hA : ∀ x y, A.Accepts (F.G x y) (F.inp x y) T ↔ disj x y = true) :
    Fintype.card ι ≤ T * (2 * (F.Ecut.card * B)) + 2 :=
  F.lowerBound A T disj hA _ fun _ _ hP hc => Protocol.disj_lowerBound hP hc

omit [DecidableEq V] in
/-- Theorem 1.1 for the complement of set disjointness (the predicate holds iff the inputs
intersect, as in all constructions of Bachrach et al.). -/
theorem not_disj_lowerBound {ι : Type*} [Fintype ι] [Finite V]
    (F : LBFamily (ι → Bool) (ι → Bool) V I) [∀ x y, DecidableRel (F.G x y).Adj]
    (A : Algorithm V I σ B) (T : ℕ)
    (hA : ∀ x y, A.Accepts (F.G x y) (F.inp x y) T ↔ disj x y = false) :
    Fintype.card ι ≤ T * (2 * (F.Ecut.card * B)) + 2 :=
  F.lowerBound A T (fun x y => !disj x y) (fun x y => by simpa using hA x y) _
    fun _ _ hP hc => Protocol.not_disj_lowerBound hP hc

omit [DecidableEq V] in
/-- Theorem 1.1 for the complement of set disjointness, for algorithms that are only required to
be correct on the graphs `G x y` with `x ≠ 0` or `y ≠ 0` (e.g. because `G 0 0` is disconnected
and the algorithm is only required to work on connected networks). -/
theorem not_disj_lowerBound_of_ne_zero {ι : Type*} [Fintype ι] [Finite V]
    (F : LBFamily (ι → Bool) (ι → Bool) V I) [∀ x y, DecidableRel (F.G x y).Adj]
    (A : Algorithm V I σ B) (T : ℕ)
    (hA : ∀ x y, ((∃ i, x i = true) ∨ ∃ i, y i = true) →
      (A.Accepts (F.G x y) (F.inp x y) T ↔ disj x y = false)) :
    Fintype.card ι ≤ T * (2 * (F.Ecut.card * B)) + 2 := by
  have := Fintype.ofFinite V
  obtain ⟨P, hc, hP⟩ := F.simulation A T
  refine Protocol.not_disj_lowerBound_of_ne_zero (P := P) (fun x y hxy => ?_) hc
  rw [hP x y]
  cases h : disj x y <;> simp [hA x y hxy, h]

end LBFamily

/-- A family of lower bound graphs in which every node's input is its neighbourhood
(`inp x y v w = true` iff `v` and `w` are adjacent). -/
def LBFamily.ofAdj {X Y V : Type*} (G : X → Y → SimpleGraph V) [∀ x y, DecidableRel (G x y).Adj]
    (alice : V → Bool) (Ecut : Finset (V × V))
    (Ecut_sub : ∀ p ∈ Ecut, alice p.1 = true ∧ alice p.2 = false)
    (adj_cut : ∀ x y a b, alice a = true → alice b = false → (G x y).Adj a b → (a, b) ∈ Ecut)
    (adj_alice : ∀ x y y' a b, alice a = true → alice b = true →
      ((G x y).Adj a b ↔ (G x y').Adj a b))
    (adj_bob : ∀ x x' y a b, alice a = false → alice b = false →
      ((G x y).Adj a b ↔ (G x' y).Adj a b))
    (adj_fixed : ∀ x x' y y' a b, alice a = true → alice b = false →
      ((G x y).Adj a b ↔ (G x' y').Adj a b)) :
    LBFamily X Y V (V → Bool) where
  G := G
  inp x y v w := decide ((G x y).Adj v w)
  alice := alice
  Ecut := Ecut
  Ecut_sub := Ecut_sub
  adj_cut := adj_cut
  adj_alice := adj_alice
  adj_bob := adj_bob
  adj_fixed := adj_fixed
  inp_alice x y y' v hv := by
    funext w
    congr 1
    apply propext
    cases hw : alice w
    · exact adj_fixed x x y y' v w hv hw
    · exact adj_alice x y y' v w hv hw
  inp_bob x x' y v hv := by
    funext w
    congr 1
    apply propext
    cases hw : alice w
    · exact adj_bob x x' y v w hv hw
    · rw [(G x y).adj_comm, (G x' y).adj_comm]
      exact adj_fixed x x' y y w v hw hv

end Cslib.Congest
