/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Sync

/-!
# FLM: no synchronous unauthenticated weak consensus for `3 ≤ n ≤ 3t`

Fischer, Lynch and Merritt [FischerLynchMerritt1986]: Byzantine consensus with **weak validity** (if
all processes are correct and propose `v`, then `v` is decided) is impossible without signatures if
`n ≤ 3t`, even in synchrony. This is used, e.g., in Lemma 10 of [CivitEtAl2024].

The lock-step model has its own version of the covering argument,
`Cslib.Byzantine.LockStep.CoverSystem` (on arbitrary communication graphs, with partial
neighbourhoods); the version here works directly with partially synchronous runs, so that it
applies to algorithms stated in that model.

We prove it in the shared partially synchronous model (`Cslib.Byzantine.PartialSync.Model`), for
synchronous runs (`gst = 0`, `SolvesConsensusSync`), for every `δ`.

## Covering systems

A `CoverSystem P Q VI` is a "network of copies": every node `x : Q` runs the code of process
`proc x` with proposal `inp x`, and listens, as messages from sender `q`, to what node `nbr x q`
sends. Its states `CoverSystem.st A C τ x` are computed in lock step, independently of any run.

* `CoverSystem.run`: given a set `F` of faulty processes and a *lift* `lift : P → Q` of the
  correct processes, the synchronous run in which every faulty `q` sends to `p` what the node
  `nbr (lift p) q` would send. If the lift is compatible with `nbr` on correct processes, the
  correct processes have the states of their lifts (`CoverSystem.st_run`).
* `CoverSystem.st_map`: states are preserved by (local) morphisms of covering systems; this
  gives both "the fault-free run is a covering system" and *locality* (the state of a node at
  time `τ` only depends on the inputs of nodes at distance `≤ τ`).

## The proof (on an infinite line instead of a ring)

Split `P` into three nonempty groups `G 0, G 1, G 2` of size `≤ t` (`exists_label`; here `3 ≤ n`
is used). The *line* (`CoverSystem.line`) has a copy of `G (u mod 3)` at every node `u ∈ ℤ`, with
input `v₀` for `u < 0` and `v₁` for `u ≥ 0`; a copy listens to the nearest copies (offset
`-1, 0, 1`) of the other groups. For every `u`, the copies at nodes `u, u + 1` are the correct
processes of a valid synchronous run in which the group of `u + 2` is Byzantine; hence by
Termination and Agreement all copies along the line decide the same value. By locality, a copy far
left behaves as in the fault-free run with all inputs `v₀` (so it decides `v₀` by weak validity),
and a copy far right decides `v₁`. Contradiction.

The hypothesis `3 ≤ n` is essential: for `n = 2`, `t = 1` the algorithm "exchange proposals,
decide your own proposal if both coincide, a default value otherwise" solves weak consensus.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

open Finset

/-- A covering system: node `x` runs the code of `proc x` with proposal `inp x` and receives, as
messages from `q`, what node `nbr x q` sends. -/
structure CoverSystem (P Q VI : Type*) where
  /-- The process whose code node `x` runs. -/
  proc : Q → P
  /-- `nbr x q`: the node whose messages `x` receives as messages from `q`. -/
  nbr : Q → P → Q
  /-- The proposal of node `x`. -/
  inp : Q → VI

namespace CoverSystem

variable {P Q Q' M S VI VO : Type*} (A : Algorithm P M S VI VO) (C : CoverSystem P Q VI)

/-- The states of the nodes of a covering system (lock-step synchronous execution). -/
def st : ℕ → Q → S
  | 0, x => A.init (C.proc x) (C.inp x)
  | τ + 1, x => A.step (C.proc x) (st τ x) fun q => A.send q (st τ (C.nbr x q)) (C.proc x)

@[simp] theorem st_zero (x : Q) : C.st A 0 x = A.init (C.proc x) (C.inp x) := rfl

theorem st_succ (τ : ℕ) (x : Q) :
    C.st A (τ + 1) x =
      A.step (C.proc x) (C.st A τ x) fun q => A.send q (C.st A τ (C.nbr x q)) (C.proc x) := rfl

/-- Node `x` decides `v` at some time. -/
def Decides (x : Q) (v : VO) : Prop := ∃ τ, A.decide (C.proc x) (C.st A τ x) = some v

/-- **Morphisms of covering systems preserve states.** Let `f : Q → Q'` and let `Sτ τ` be sets
of nodes (where the comparison is claimed at time `τ`), shrinking in time and closed under
looking one step back along `nbr`. If `f` respects the code, the neighbours and the inputs on
these sets, then `x` and `f x` have the same states. -/
theorem st_map {C' : CoverSystem P Q' VI} (f : Q → Q') (Sτ : ℕ → Set Q)
    (hp : ∀ x, C'.proc (f x) = C.proc x)
    (hS : ∀ τ, ∀ x ∈ Sτ (τ + 1), x ∈ Sτ τ)
    (hn : ∀ τ, ∀ x ∈ Sτ (τ + 1), ∀ q, C'.nbr (f x) q = f (C.nbr x q) ∧ C.nbr x q ∈ Sτ τ)
    (hi : ∀ x ∈ Sτ 0, C'.inp (f x) = C.inp x) :
    ∀ τ, ∀ x ∈ Sτ τ, C'.st A τ (f x) = C.st A τ x := by
  intro τ
  induction τ with
  | zero => intro x hx; simp [hp, hi x hx]
  | succ τ ih =>
    intro x hx
    rw [st_succ, st_succ, hp, ih x (hS τ x hx)]
    congr 1
    funext q
    rw [(hn τ x hx q).1, ih _ (hn τ x hx q).2]

variable [DecidableEq P]

/-- The synchronous run (`gst = 0`, zero delays) in which the processes of `F` are Byzantine and
every Byzantine `q` sends to `p` what node `nbr (lift p) q` sends in the covering system. -/
def run (F : Finset P) (lift : P → Q) : Run P M VI where
  faulty := F
  inp p := C.inp (lift p)
  gst := 0
  byz q τ p := A.send q (C.st A τ (C.nbr (lift p) q)) p
  dl _ τ _ := τ

omit [DecidableEq P] in
@[simp] theorem run_faulty (F : Finset P) (lift : P → Q) : (C.run A F lift).faulty = F := rfl

omit [DecidableEq P] in
@[simp] theorem run_gst (F : Finset P) (lift : P → Q) : (C.run A F lift).gst = 0 := rfl

omit [DecidableEq P] in
@[simp] theorem run_inp (F : Finset P) (lift : P → Q) :
    (C.run A F lift).inp = fun p => C.inp (lift p) :=
  rfl

omit [DecidableEq P] in
theorem run_valid {t δ : ℕ} {F : Finset P} (hF : F.card ≤ t) (lift : P → Q) :
    (C.run A F lift).Valid t δ where
  card_faulty := hF
  dl_ge _ _ _ _ _ := le_rfl
  dl_le _ τ _ _ _ := by simp [run]

end CoverSystem

namespace CoverSystem

variable {P Q M S VI VO : Type*} [DecidableEq P] (A : Algorithm P M S VI VO)
  (C : CoverSystem P Q VI)

/-- **Covering lemma.** If the lift maps every correct process `p` to a node running `p`'s code and
correct neighbours to the designated neighbours, then correct processes have the states of their
lifts. -/
theorem st_run {F : Finset P} {lift : P → Q} (hproc : ∀ p ∉ F, C.proc (lift p) = p)
    (hnbr : ∀ p ∉ F, ∀ q ∉ F, C.nbr (lift p) q = lift q) :
    ∀ τ, ∀ p ∉ F, (C.run A F lift).st A τ p = C.st A τ (lift p) := by
  intro τ
  induction τ with
  | zero => intro p hp; simp [hproc p hp, run]
  | succ τ ih =>
    intro p hp
    rw [Run.st_succ, st_succ, hproc p hp, ih p hp]
    congr 1
    funext q
    rw [Run.inbox_of_dl_eq A (fun _ _ _ => rfl)]
    by_cases hq : q ∈ F
    · rw [Run.out_of_faulty A _ hq]; rfl
    · rw [Run.out_of_correct A _ hq, ih q hq, hnbr p hp q hq]

theorem decides_run_iff {F : Finset P} {lift : P → Q} (hproc : ∀ p ∉ F, C.proc (lift p) = p)
    (hnbr : ∀ p ∉ F, ∀ q ∉ F, C.nbr (lift p) q = lift q) {p : P} (hp : p ∉ F) {v : VO} :
    (C.run A F lift).Decides A p v ↔ C.Decides A (lift p) v := by
  simp only [Run.Decides, CoverSystem.Decides, st_run A C hproc hnbr _ p hp, hproc p hp]

end CoverSystem

/-! ### The trivial covering system (fault-free runs) and the line -/

namespace CoverSystem

variable {P M S VI VO : Type*}

/-- The fault-free system: every process is its own node, with proposal `c p`. -/
def triv (c : P → VI) : CoverSystem P P VI where
  proc := id
  nbr _ q := q
  inp := c

/-- Offset (`0`, `+1` or `-1`) from a node of label `u` to the nearest node of label `≡ u + d`. -/
def lineOff (d : ℤ) : ℤ := if d % 3 = 1 then 1 else if d % 3 = 2 then -1 else 0

theorem abs_lineOff_le (d : ℤ) : -1 ≤ lineOff d ∧ lineOff d ≤ 1 := by
  unfold lineOff; split_ifs <;> omega

/-- The *line*: nodes `(u, p) : ℤ × P` (meaningful when `g p ≡ u mod 3`); node `(u, p)` runs
`p` with proposal `xs u` and listens to the copy of `q` at the nearest node `u' ∈ {u-1, u, u+1}`
with `u' ≡ g q mod 3`. -/
def line (g : P → ℤ) (xs : ℤ → VI) : CoverSystem P (ℤ × P) VI where
  proc x := x.2
  nbr x q := (x.1 + lineOff (g q - x.1), q)
  inp x := xs x.1

/-- The faulty processes of the `u`-th pair run: the group of label `u + 2`. -/
def pairFaulty [Fintype P] (g : P → ℤ) (u : ℤ) : Finset P :=
  univ.filter fun q => (g q - u) % 3 = 2

/-- The lift of the `u`-th pair run: groups `u` and `u + 1` are mapped to nodes `u` and `u + 1`. -/
def pairLift (g : P → ℤ) (u : ℤ) (p : P) : ℤ × P :=
  (if (g p - u) % 3 = 0 then u else u + 1, p)

theorem pair_nbr [Fintype P] (g : P → ℤ) (xs : ℤ → VI) (u : ℤ) :
    ∀ p ∉ pairFaulty g u, ∀ q ∉ pairFaulty g u,
      (line g xs).nbr (pairLift g u p) q = pairLift g u q := by
  intro p hp q hq
  simp only [pairFaulty, mem_filter, mem_univ, true_and] at hp hq
  simp only [line, pairLift, Prod.mk.injEq, and_true]
  unfold lineOff
  split_ifs <;> omega

/-- **Locality** (left end): if all nodes `u < 0` of the line have proposal `b`, a node `(u, p)`
with `u + τ < 0` has at time `τ` the state of `p` in the fault-free system with all proposals
`b`. -/
theorem line_st_left (A : Algorithm P M S VI VO) (g : P → ℤ) (xs : ℤ → VI) (b : VI)
    (hb : ∀ u < 0, xs u = b) :
    ∀ (τ : ℕ) (u : ℤ) p, u + τ < 0 → (triv fun _ => b).st A τ p = (line g xs).st A τ (u, p) := by
  intro τ u p h
  refine (line g xs).st_map A (C' := triv fun _ => b) Prod.snd (fun τ => {x | x.1 + τ < 0})
    (fun _ => rfl) (fun τ x hx => by simp at hx ⊢; omega) (fun τ x hx q => ⟨rfl, ?_⟩)
    (fun x hx => (hb x.1 (by simpa using hx)).symm) τ (u, p) h
  have := abs_lineOff_le (g q - x.1)
  simp only [Set.mem_ofPred_eq] at hx ⊢
  simp only [line]; omega

/-- **Locality** (right end): if all nodes `u ≥ 0` of the line have proposal `b`, a node `(u, p)`
with `0 ≤ u - τ` has at time `τ` the state of `p` in the fault-free system with all proposals
`b`. -/
theorem line_st_right (A : Algorithm P M S VI VO) (g : P → ℤ) (xs : ℤ → VI) (b : VI)
    (hb : ∀ u, 0 ≤ u → xs u = b) :
    ∀ (τ : ℕ) (u : ℤ) p, 0 ≤ u - τ → (triv fun _ => b).st A τ p = (line g xs).st A τ (u, p) := by
  intro τ u p h
  refine (line g xs).st_map A (C' := triv fun _ => b) Prod.snd (fun τ => {x | 0 ≤ x.1 - τ})
    (fun _ => rfl) (fun τ x hx => by simp at hx ⊢; omega) (fun τ x hx q => ⟨rfl, ?_⟩)
    (fun x hx => (hb x.1 (by simpa using hx)).symm) τ (u, p) h
  have := abs_lineOff_le (g q - x.1)
  simp only [Set.mem_ofPred_eq] at hx ⊢
  simp only [line]; omega

end CoverSystem

/-- A labelling of the processes by `{0, 1, 2}`, such that every residue class mod `3` is
nonempty and has at most `t` elements. Requires `3 ≤ n ≤ 3t`. -/
theorem exists_label {P : Type*} [Fintype P] {t : ℕ}
    (h3 : 3 ≤ Fintype.card P) (hn : Fintype.card P ≤ 3 * t) :
    ∃ g : P → ℤ, (∀ p, 0 ≤ g p ∧ g p < 3) ∧ (∀ u : ℤ, ∃ p, (g p - u) % 3 = 0) ∧
      ∀ u : ℤ, (univ.filter fun q => (g q - u) % 3 = 2).card ≤ t := by
  classical
  set e := Fintype.equivFin P
  refine ⟨fun p => ((e p : ℕ) % 3 : ℕ), fun p => by dsimp only; omega, fun u => ?_, fun u => ?_⟩
  · refine ⟨e.symm ⟨(u % 3).toNat, by omega⟩, ?_⟩
    simp only [Equiv.apply_symm_apply]
    omega
  · calc (univ.filter fun q => (((e q : ℕ) % 3 : ℕ) - u) % 3 = 2).card
        ≤ (range t).card := by
          refine card_le_card_of_injOn (fun q => (e q : ℕ) / 3) (fun q _ => ?_) ?_
          · have := (e q).isLt
            simp only [coe_range, Set.mem_Iio]
            omega
          · intro q hq q' hq' hqq
            simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hq hq'
            simp only at hqq
            apply e.injective
            apply Fin.ext
            omega
      _ = t := card_range t

section Main

variable {P M S V : Type*} [Fintype P] [DecidableEq P] {t δ : ℕ}

open CoverSystem

omit [Fintype P] in
/-- In the fault-free synchronous system with all proposals `b`, every process decides `b`
(Termination and weak validity). -/
theorem triv_decides {A : Algorithm P M S V V} (hA : SolvesConsensusSync t δ A (weakValidity P V))
    (b : V) (p : P) : ∃ τ, A.decide p ((triv fun _ : P => b).st A τ p) = some b := by
  set C := triv (P := P) fun _ => b
  have hproc : ∀ p ∉ (∅ : Finset P), C.proc (id p) = p := fun _ _ => rfl
  have hnbr : ∀ p ∉ (∅ : Finset P), ∀ q ∉ (∅ : Finset P), C.nbr (id p) q = id q :=
    fun _ _ _ _ => rfl
  have hV : (C.run A ∅ id).Valid t δ := C.run_valid A (by simp) id
  obtain ⟨v, hv⟩ := hA.termination _ hV (Run.authValid_none A _) rfl p (by simp)
  have hval := hA.validity _ hV (Run.authValid_none A _) rfl p (by simp) v hv
  have : v = b := hval b fun q => by simp [Run.inputConf, run, C, triv]
  subst this
  exact (C.decides_run_iff A hproc hnbr (by simp)).1 hv

/-- **Fischer–Lynch–Merritt** (1986), for any two distinct values: no algorithm solves
unauthenticated Byzantine consensus with weak validity in synchrony if `3 ≤ n ≤ 3t`.
See [FischerLynchMerritt1986].
The hypothesis `3 ≤ n` is necessary: for `n = 2`, `t = 1`, "exchange proposals and decide your
own one if both coincide, a default value otherwise" solves weak consensus. -/
theorem weakValidity_not_solvesConsensusSync_of_ne {v₀ v₁ : V} (hv : v₀ ≠ v₁)
    (A : Algorithm P M S V V) (h3 : 3 ≤ Fintype.card P) (hn : Fintype.card P ≤ 3 * t) :
    ¬ SolvesConsensusSync t δ A (weakValidity P V) := by
  intro hA
  obtain ⟨g, hg3, hg, hgt⟩ := exists_label h3 hn
  set xs : ℤ → V := fun u => if 0 ≤ u then v₁ else v₀
  set L := line g xs
  have hproc : ∀ u, ∀ p ∉ pairFaulty g u, L.proc (pairLift g u p) = p := fun _ _ _ => rfl
  have hV : ∀ u, (L.run A (pairFaulty g u) (pairLift g u)).Valid t δ :=
    fun u => L.run_valid A (hgt u) _
  have lift0 : ∀ u p, (g p - u) % 3 = 0 → p ∉ pairFaulty g u ∧ pairLift g u p = (u, p) := by
    intro u p hp
    simp [pairFaulty, pairLift, hp]
  have lift1 : ∀ u p, (g p - (u + 1)) % 3 = 0 →
      p ∉ pairFaulty g u ∧ pairLift g u p = (u + 1, p) := by
    intro u p hp
    simp only [pairFaulty, mem_filter, mem_univ, true_and, pairLift]
    refine ⟨by omega, ?_⟩
    simp only [show ¬ (g p - u) % 3 = 0 by omega, ↓reduceIte]
  have term : ∀ u p, (g p - u) % 3 = 0 → ∃ v, L.Decides A (u, p) v := by
    intro u p hp
    obtain ⟨hpF, hl⟩ := lift0 u p hp
    obtain ⟨v, hv⟩ := hA.termination _ (hV u) (Run.authValid_none A _) rfl p hpF
    refine ⟨v, ?_⟩
    rw [← hl]
    exact (L.decides_run_iff A (hproc u) (pair_nbr g xs u) hpF).1 hv
  have agree : ∀ u p q, p ∉ pairFaulty g u → q ∉ pairFaulty g u → ∀ v w,
      L.Decides A (pairLift g u p) v → L.Decides A (pairLift g u q) w → v = w := by
    intro u p q hp hq v w hpv hqw
    exact hA.agreement _ (hV u) (Run.authValid_none A _) rfl p hp q hq v w
      ((L.decides_run_iff A (hproc u) (pair_nbr g xs u) hp).2 hpv)
      ((L.decides_run_iff A (hproc u) (pair_nbr g xs u) hq).2 hqw)
  obtain ⟨p, -⟩ := hg 0
  obtain ⟨τ₀, hτ₀⟩ := triv_decides hA v₀ p
  obtain ⟨τ₁, hτ₁⟩ := triv_decides hA v₁ p
  have hp3 := hg3 p
  set u₀ : ℤ := g p - 3 * (τ₀ + 1)
  have hdec₀ : L.Decides A (u₀, p) v₀ := by
    refine ⟨τ₀, ?_⟩
    rw [← line_st_left A g xs v₀ (fun u hu => by simp [xs, not_le.2 hu]) τ₀ u₀ p (by omega)]
    exact hτ₀
  have hdec₁ : L.Decides A (u₀ + ((3 * (τ₀ + τ₁ + 2) : ℕ) : ℤ), p) v₁ := by
    refine ⟨τ₁, ?_⟩
    rw [← line_st_right A g xs v₁ (fun u hu => by simp [xs, hu]) τ₁ _ p (by push_cast; omega)]
    exact hτ₁
  have chain : ∀ k : ℕ, ∀ q, (g q - (u₀ + k)) % 3 = 0 → ∀ w,
      L.Decides A (u₀ + k, q) w → w = v₀ := by
    intro k
    induction k with
    | zero =>
      intro q hq w hw
      have h00 : u₀ + ((0 : ℕ) : ℤ) = u₀ := by simp
      rw [h00] at hq hw
      have h0 : (g p - u₀) % 3 = 0 := by omega
      obtain ⟨hpF, hpl⟩ := lift0 u₀ p h0
      obtain ⟨hqF, hql⟩ := lift0 u₀ q hq
      rw [← hpl] at hdec₀
      rw [← hql] at hw
      exact (agree u₀ p q hpF hqF v₀ w hdec₀ hw).symm
    | succ k ih =>
      intro q hq w hw
      have hk : u₀ + ((k + 1 : ℕ) : ℤ) = (u₀ + k) + 1 := by push_cast; omega
      rw [hk] at hq hw
      obtain ⟨r, hr⟩ := hg (u₀ + k)
      obtain ⟨v, hrv⟩ := term _ r hr
      have := ih r hr v hrv
      obtain ⟨hrF, hrl⟩ := lift0 _ r hr
      obtain ⟨hqF, hql⟩ := lift1 _ q hq
      rw [← hrl] at hrv
      rw [← hql] at hw
      rw [← agree _ r q hrF hqF v w hrv hw, this]
  exact hv (chain _ p (by push_cast; omega) v₁ hdec₁).symm

/-- **Fischer–Lynch–Merritt** (1986): no algorithm solves unauthenticated binary Byzantine
consensus with weak validity in synchrony if `3 ≤ n ≤ 3t` (any `δ`) [FischerLynchMerritt1986].
The hypothesis `3 ≤ n` is necessary: the statement is false for `n = 2`, `t = 1`
("exchange proposals, decide your own if both coincide, a default value otherwise"). -/
theorem weakValidity_not_solvesConsensusSync (A : Algorithm P M S Bool Bool)
    (h3 : 3 ≤ Fintype.card P) (hn : Fintype.card P ≤ 3 * t) :
    ¬ SolvesConsensusSync t δ A (weakValidity P Bool) :=
  weakValidity_not_solvesConsensusSync_of_ne Bool.false_ne_true A h3 hn

/-- **Fischer–Lynch–Merritt** (1986): weak validity is not solvable without signatures in
synchrony if `3 ≤ n ≤ 3t`, for any two distinct values. -/
theorem weakValidity_not_solvableSync_of_ne {v₀ v₁ : V} (hv : v₀ ≠ v₁)
    (h3 : 3 ≤ Fintype.card P) (hn : Fintype.card P ≤ 3 * t) :
    ¬ (weakValidity P V).SolvableSync t δ := by
  rintro ⟨M, S, A, hA⟩
  exact weakValidity_not_solvesConsensusSync_of_ne hv A h3 hn hA

/-- **Fischer–Lynch–Merritt** (1986): binary weak consensus is not solvable without signatures in
synchrony if `3 ≤ n ≤ 3t` [FischerLynchMerritt1986]. -/
theorem weakValidity_not_solvableSync (h3 : 3 ≤ Fintype.card P) (hn : Fintype.card P ≤ 3 * t) :
    ¬ (weakValidity P Bool).SolvableSync t δ :=
  weakValidity_not_solvableSync_of_ne Bool.false_ne_true h3 hn

end Main

end Cslib.Byzantine.PartialSync
