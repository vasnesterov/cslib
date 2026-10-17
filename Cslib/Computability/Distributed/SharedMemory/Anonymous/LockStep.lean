/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Anonymous
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Symmetric lock-step executions of symmetric algorithms in anonymous memory

The impossibility proofs for symmetric algorithms in memory-anonymous systems (Taubenfeld,
PODC 2017; Aghazadeh et al., PODC 2019, Theorem 5; Godard et al., PODC 2020, Theorem 1) all run
the processes in *lock-step* from a rotationally symmetric configuration and show that symmetry
is never broken. This file provides that argument once, for any high-level object `O`.

## Set-up

`SymAlg.LSSetup k g e σ sh a ids π`: there are `k` groups of `g` processes; `e q i` is the
`i`-th member of group `q` (`q < k`, `i < g`, all distinct). Member `e q i` sees the registers
rotated by `sh ^ i` (`π (e q i) = sh ^ i`) and has identifier `σ ^ i (a q)`, where
`σ ^ g = 1`, `sh ^ g = 1` and the `g` rotations `sh ^ i` of a register are pairwise distinct.
The processes need not cover all of `P` (a one-group set-up is `LSSetup.single`).

A configuration is *symmetric* (`SymAlg.SymCfg k g e σ sh C s b`) if for every group `q` the
member `e q i` is in local state `σ ^ i • s q` with pending operation `b q`, and the memory
satisfies `mem (sh y) = σ • mem y`.

## Rounds

A *group round* of group `q` lets each member `e q 0, …, e q (g-1)` take one step, in this
order. From a symmetric configuration, all members of the group perform the same kind of access
on `g` *different* physical registers `sh ^ i x`, so the sequential round has the same effect as
a simultaneous one and the configuration stays symmetric (`round_rmw`, `round_snap`); likewise
for a round of responses (`round_ret`; responses do not involve identifiers, so all members
return the same response) and of invocations (`round_inv`). The initial configuration is
symmetric (`symCfg_init`).

## Auxiliary results

* `Impl.runFrom_range`: run the labels `lab 0, …, lab (n-1)` given a step-indexed invariant;
* `val_finRotate_pow_apply`, `finRotate_pow_pow_eq_one`, `finRotate_pow_pow_apply_inj`: the
  rotation `sh = finRotate m ^ d` with `d * g = m` has order `g` on every register.
-/

@[expose] public section

open Cslib.SharedMemory

/-! ### Rotations of `Fin m` -/

/-- The value of `finRotate m ^ k` applied to `x` is `(x + k) % m`. -/
lemma val_finRotate_pow_apply {m : ℕ} (k : ℕ) (x : Fin m) :
    (((finRotate m) ^ k) x : ℕ) = (x + k) % m := by
  rcases m with _ | m
  · exact x.elim0
  induction k with
  | zero => simp [Nat.mod_eq_of_lt x.isLt]
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
      ← Nat.add_mod, Nat.add_assoc]

/-- Rotating `m = d * g` registers by `d` positions has order dividing `g`. -/
lemma finRotate_pow_pow_eq_one {m d g : ℕ} (h : d * g = m) : ((finRotate m) ^ d) ^ g = 1 := by
  ext x
  rw [← pow_mul, val_finRotate_pow_apply, h, Equiv.Perm.one_apply, Nat.add_mod_right,
    Nat.mod_eq_of_lt x.isLt]

/-- Rotating `m = d * g` registers by `d` positions: the `g` rotations of a register are
pairwise distinct. -/
lemma finRotate_pow_pow_apply_inj {m d g : ℕ} (h : d * g = m) {i j : ℕ} (hi : i < g)
    (hj : j < g) {y : Fin m} (hij : (((finRotate m) ^ d) ^ i) y = (((finRotate m) ^ d) ^ j) y) :
    i = j := by
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, zero_mul] at h; exact absurd y.isLt (by omega)
    · exact h0
  have := congrArg Fin.val hij
  rw [← pow_mul, ← pow_mul, val_finRotate_pow_apply, val_finRotate_pow_apply] at this
  have hmod : Nat.ModEq m (d * i) (d * j) := Nat.ModEq.add_left_cancel' (y : ℕ) this
  have := hmod.eq_of_lt_of_lt (by rw [← h]; exact Nat.mul_lt_mul_of_pos_left hi hd0)
    (by rw [← h]; exact Nat.mul_lt_mul_of_pos_left hj hd0)
  exact Nat.eq_of_mul_eq_mul_left hd0 this

namespace Cslib.SharedMemory

/-- Run the labels `lab 0, …, lab (n-1)` from `C`, given an invariant `Q j` that holds before
the `j`-th label and is re-established by it. -/
lemma Impl.runFrom_range {O : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type}
    [DecidableEq P] (I : Impl O B P L) (Q : ℕ → Config O B P L → Prop) (lab : ℕ → Label P O)
    (n : ℕ) (C : Config O B P L) (h0 : Q 0 C)
    (hstep : ∀ j < n, ∀ D, Q j D → ∃ D', I.step D (lab j) = some D' ∧ Q (j + 1) D') :
    ∃ D, I.runFrom C ((List.range n).map lab) = some D ∧ Q n D := by
  induction n with
  | zero => exact ⟨C, rfl, h0⟩
  | succ n ih =>
    obtain ⟨D, hD, hQ⟩ := ih (fun j hj => hstep j (by omega))
    obtain ⟨D', hD', hQ'⟩ := hstep n (by omega) D hQ
    refine ⟨D', ?_, hQ'⟩
    rw [List.range_succ, List.map_append, I.runFrom_append_of_eq hD, List.map_singleton,
      I.runFrom_singleton, hD']

namespace SymAlg

variable {O : ObjSpec} {Id V S : Type} {m : ℕ} [MulAction (Equiv.Perm Id) V]
  [MulAction (Equiv.Perm Id) S] {A : SymAlg O Id m V S} {P : Type}
  {ids : P → Id} {π : P → Equiv.Perm (Fin m)}

/-- The rotation set-up of a lock-step execution: `k` groups of `g` distinct processes `e q i`;
member `e q i` sees the memory rotated by `sh ^ i` and has identifier `σ ^ i (a q)`. -/
structure LSSetup (k g : ℕ) (e : ℕ → ℕ → P) (σ : Equiv.Perm Id) (sh : Equiv.Perm (Fin m))
    (a : ℕ → Id) (ids : P → Id) (π : P → Equiv.Perm (Fin m)) : Prop where
  /-- The identifier renaming has order dividing `g`. -/
  σpow : σ ^ g = 1
  /-- The register rotation has order dividing `g`. -/
  shpow : sh ^ g = 1
  /-- The `g` rotations of a register are pairwise distinct. -/
  shinj : ∀ i j y, i < g → j < g → (sh ^ i) y = (sh ^ j) y → i = j
  /-- The members of the groups are pairwise distinct. -/
  einj : ∀ q i q' j, q < k → i < g → q' < k → j < g → e q i = e q' j → q = q' ∧ i = j
  /-- Member `i` of every group sees the memory rotated by `sh ^ i`. -/
  hπ : ∀ q < k, ∀ i < g, π (e q i) = sh ^ i
  /-- Member `i` of group `q` has identifier `σ ^ i (a q)`. -/
  hid : ∀ q < k, ∀ i < g, ids (e q i) = (σ ^ i) (a q)

/-- A symmetric configuration: the members of group `q` are in local states `σ ^ i • s q` with
pending operation `b q`, and the memory is invariant under the rotation `sh` up to `σ`. -/
structure SymCfg (k g : ℕ) (e : ℕ → ℕ → P) (σ : Equiv.Perm Id) (sh : Equiv.Perm (Fin m))
    (C : A.Cfg) (s : ℕ → S) (b : ℕ → Option O.Op) : Prop where
  /-- Local states of the group members. -/
  loc : ∀ q < k, ∀ i < g, C.loc (e q i) = (σ ^ i) • s q
  /-- Pending operations of the group members. -/
  pend : ∀ q < k, ∀ i < g, C.pend (e q i) = b q
  /-- Rotational symmetry of the memory. -/
  mem : ∀ y, C.mem () (sh y) = σ • C.mem () y

variable {k g : ℕ} {e : ℕ → ℕ → P} {σ : Equiv.Perm Id} {sh : Equiv.Perm (Fin m)} {a : ℕ → Id}

/-- A one-group set-up (`k = 1`). -/
lemma LSSetup.single {e : ℕ → P} {a₀ : Id} (σpow : σ ^ g = 1) (shpow : sh ^ g = 1)
    (shinj : ∀ i j y, i < g → j < g → (sh ^ i) y = (sh ^ j) y → i = j)
    (einj : ∀ i j, i < g → j < g → e i = e j → i = j) (hπ : ∀ i < g, π (e i) = sh ^ i)
    (hid : ∀ i < g, ids (e i) = (σ ^ i) a₀) :
    LSSetup 1 g (fun _ => e) σ sh (fun _ => a₀) ids π where
  σpow := σpow
  shpow := shpow
  shinj := shinj
  einj q i q' j hq hi hq' hj h := ⟨by omega, einj i j hi hj h⟩
  hπ _ _ i hi := hπ i hi
  hid _ _ i hi := hid i hi

/-- Members of different groups are different processes. -/
lemma LSSetup.ne_of_group_ne (hS : LSSetup k g e σ sh a ids π) {q q' i j : ℕ} (hq : q < k)
    (hq' : q' < k) (hi : i < g) (hj : j < g) (hne : q ≠ q') : e q i ≠ e q' j :=
  fun h => hne (hS.einj q i q' j hq hi hq' hj h).1

/-- Different members of the same group are different processes. -/
lemma LSSetup.ne_of_ne (hS : LSSetup k g e σ sh a ids π) {q i j : ℕ} (hq : q < k) (hi : i < g)
    (hj : j < g) (hne : i ≠ j) : e q i ≠ e q j :=
  fun h => hne (hS.einj q i q j hq hi hq hj h).2

/-- In a symmetric configuration, register `sh ^ i y` holds the `σ ^ i`-renaming of the value of
register `y`. -/
lemma SymCfg.mem_pow {C : A.Cfg} {s : ℕ → S} {b : ℕ → Option O.Op}
    (hC : SymCfg k g e σ sh C s b) (i : ℕ) (y : Fin m) :
    C.mem () ((sh ^ i) y) = (σ ^ i) • C.mem () y := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, hC.mem, ih, pow_succ', mul_smul]

/-- The bookkeeping step of a group round: updating the entries `i < g` of a family indexed by
the group members, one member at a time. -/
private lemma update_round [DecidableEq P] {X : Type} {F : P → X} {q j : ℕ} {u v : ℕ → X}
    (hS : LSSetup k g e σ sh a ids π) (hq : q < k) (hj : j < g)
    (h : ∀ i < g, F (e q i) = if i < j then u i else v i) :
    ∀ i < g, Function.update F (e q j) (u j) (e q i) = if i < j + 1 then u i else v i := by
  intro i hi
  by_cases hij : i = j
  · subst hij; simp
  · rw [Function.update_of_ne (hS.ne_of_ne hq hi hj hij), h i hi]
    by_cases hi' : i < j
    · simp [hi', show i < j + 1 by omega]
    · simp [hi', show ¬ i < j + 1 by omega]

/-- Memory after a round of `rmw x f` by the `g` members of a group: if the registers
`sh ^ i x` now hold `σ ^ i • w` and the others are unchanged, the memory is still symmetric. -/
lemma LSSetup.mem_symm_of_round (hS : LSSetup k g e σ sh a ids π) {M M' : Fin m → V}
    (hM : ∀ y, M (sh y) = σ • M y) {x : Fin m} {w : V} (hg : 0 < g)
    (h3 : ∀ i < g, M' ((sh ^ i) x) = (σ ^ i) • w)
    (h4 : ∀ y, (∀ i < g, (sh ^ i) x ≠ y) → M' y = M y) : ∀ y, M' (sh y) = σ • M' y := by
  intro y
  by_cases hy : ∃ i < g, (sh ^ i) x = y
  · obtain ⟨i, hi, rfl⟩ := hy
    rw [h3 i hi]
    by_cases hi1 : i + 1 < g
    · have := h3 (i + 1) hi1
      rw [pow_succ', Equiv.Perm.mul_apply] at this
      rw [this, pow_succ', mul_smul]
    · have hig : i + 1 = g := by omega
      have : sh ((sh ^ i) x) = x := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ', hig, hS.shpow]; rfl
      rw [this]
      have h0 := h3 0 hg
      simp only [pow_zero, Equiv.Perm.one_apply, one_smul] at h0
      rw [h0, smul_smul, ← pow_succ', hig, hS.σpow, one_smul]
  · push Not at hy
    have hy' : ∀ i < g, (sh ^ i) x ≠ sh y := by
      intro i hi h
      rcases i with _ | i
      · apply hy (g - 1) (by omega)
        have : (sh ^ (g - 1)) (sh y) = (sh ^ g) y := by
          rw [← Equiv.Perm.mul_apply, ← pow_succ, show g - 1 + 1 = g by omega]
        rw [hS.shpow] at this
        simp only [pow_zero, Equiv.Perm.one_apply] at h
        rw [h, this]; rfl
      · apply hy i (by omega)
        rw [pow_succ', Equiv.Perm.mul_apply] at h
        exact sh.injective h
    rw [h4 _ hy', h4 _ hy, hM]

section Rounds

variable (hS : LSSetup k g e σ sh a ids π) (hA : A.Symmetric)
include hS hA

/-- The initial configuration is symmetric. -/
lemma symCfg_init :
    SymCfg k g e σ sh (A.impl ids π).initCfg (fun q => A.init (a q)) (fun _ => none) :=
  ⟨fun q hq i hi => by
    change A.init (ids (e q i)) = _
    rw [hS.hid q hq i hi, hA.init],
   fun _ _ _ _ => rfl, fun _ => by simp [Impl.initCfg, SymAlg.impl, hA.bot]⟩

variable [DecidableEq P]

/-- A round of read-modify-write steps of group `q` preserves symmetry. -/
lemma round_rmw {C : A.Cfg} {s : ℕ → S} {b : ℕ → Option O.Op}
    (hC : SymCfg k g e σ sh C s b) {q : ℕ} (hq : q < k) (hb : b q ≠ none) (hg : 0 < g)
    {x : Fin m} {f : V → V} {κ : V → S} (hact : A.act (s q) = .rmw x f κ) :
    ∃ D, (A.impl ids π).runFrom C ((List.range g).map (fun j => .tau (e q j))) = some D ∧
      SymCfg k g e σ sh D (Function.update s q (κ (C.mem () x))) b ∧
      (∀ p, D.pend p = C.pend p) := by
  set v := C.mem () x
  let Q : ℕ → A.Cfg → Prop := fun j D =>
    (∀ i < g, D.loc (e q i) = if i < j then (σ ^ i) • κ v else (σ ^ i) • s q) ∧
    (∀ p, (∀ i < g, e q i ≠ p) → D.loc p = C.loc p) ∧
    (∀ p, D.pend p = C.pend p) ∧
    (∀ i < g, D.mem () ((sh ^ i) x) = if i < j then (σ ^ i) • f v else (σ ^ i) • v) ∧
    (∀ y, (∀ i < g, (sh ^ i) x ≠ y) → D.mem () y = C.mem () y)
  obtain ⟨D, hD, hQ1, hQ1', hQ2, hQ3, hQ4⟩ := Impl.runFrom_range (A.impl ids π) Q _ g C
    ⟨fun i hi => by simp [hC.loc q hq i hi], fun _ _ => rfl, fun _ => rfl,
      fun i hi => by simp [hC.mem_pow, v], fun _ _ => rfl⟩
    (by
      rintro j hj D ⟨h1, h1', h2, h3, h4⟩
      have hpend : D.pend (e q j) ≠ none := by rw [h2, hC.pend q hq j hj]; exact hb
      have hloc : D.loc (e q j) = (σ ^ j) • s q := by simp [h1 j hj]
      have hact' : A.act (D.loc (e q j)) = .rmw x (fun w => (σ ^ j) • f ((σ ^ j)⁻¹ • w))
          (fun w => (σ ^ j) • κ ((σ ^ j)⁻¹ • w)) := by
        rw [hloc, hA.act, hact]; rfl
      have hval : D.mem () ((sh ^ j) x) = (σ ^ j) • v := by simp [h3 j hj]
      refine ⟨_, SymAlg.impl_step_tau_rmw ids π hpend hact', ?_⟩
      simp only [hS.hπ q hq j hj, hval, inv_smul_smul]
      refine ⟨update_round hS hq hj h1, fun p hp => ?_, fun p => h2 p, fun i hi => ?_,
        fun y hy => ?_⟩
      · dsimp only; rw [Function.update_of_ne (Ne.symm (hp j hj)), h1' p hp]
      · by_cases hij : i = j
        · subst hij; simp
        · have hne : (sh ^ i) x ≠ (sh ^ j) x := fun h => hij (hS.shinj i j x hi hj h)
          simp only [Function.update_self]
          rw [Function.update_of_ne hne, h3 i hi]
          by_cases hi' : i < j
          · simp [hi', show i < j + 1 by omega]
          · simp [hi', show ¬ i < j + 1 by omega]
      · simp only [Function.update_self]
        rw [Function.update_of_ne (Ne.symm (hy j hj)), h4 y hy])
  refine ⟨D, hD, ⟨fun q' hq' i hi => ?_, fun q' hq' i hi => by rw [hQ2, hC.pend q' hq' i hi],
    hS.mem_symm_of_round hC.mem hg (w := f v) (fun i hi => by simp [hQ3 i hi, hi]) hQ4⟩, hQ2⟩
  by_cases hqq : q' = q
  · subst hqq; simp [hQ1 i hi, hi]
  · rw [hQ1' _ (fun j hj => hS.ne_of_group_ne hq hq' hj hi (Ne.symm hqq)), hC.loc q' hq' i hi,
      Function.update_of_ne hqq]

/-- A round of snapshots of group `q` preserves symmetry. -/
lemma round_snap {C : A.Cfg} {s : ℕ → S} {b : ℕ → Option O.Op}
    (hC : SymCfg k g e σ sh C s b) {q : ℕ} (hq : q < k) (hb : b q ≠ none)
    {κ : (Fin m → V) → S} (hact : A.act (s q) = .snap κ) :
    ∃ D, (A.impl ids π).runFrom C ((List.range g).map (fun j => .tau (e q j))) = some D ∧
      SymCfg k g e σ sh D (Function.update s q (κ (C.mem ()))) b ∧
      (∀ p, D.pend p = C.pend p) := by
  let Q : ℕ → A.Cfg → Prop := fun j D =>
    (∀ i < g, D.loc (e q i) = if i < j then (σ ^ i) • κ (C.mem ()) else (σ ^ i) • s q) ∧
    (∀ p, (∀ i < g, e q i ≠ p) → D.loc p = C.loc p) ∧
    (∀ p, D.pend p = C.pend p) ∧ D.mem () = C.mem ()
  obtain ⟨D, hD, hQ1, hQ1', hQ2, hQ3⟩ := Impl.runFrom_range (A.impl ids π) Q _ g C
    ⟨fun i hi => by simp [hC.loc q hq i hi], fun _ _ => rfl, fun _ => rfl, rfl⟩
    (by
      rintro j hj D ⟨h1, h1', h2, h3⟩
      have hpend : D.pend (e q j) ≠ none := by rw [h2, hC.pend q hq j hj]; exact hb
      have hloc : D.loc (e q j) = (σ ^ j) • s q := by simp [h1 j hj]
      have hact' : A.act (D.loc (e q j)) = .snap (fun w => (σ ^ j) • κ ((σ ^ j)⁻¹ • w)) := by
        rw [hloc, hA.act, hact]; rfl
      have hview : (fun y => D.mem () ((sh ^ j) y)) = (σ ^ j) • C.mem () := by
        funext y; rw [h3, hC.mem_pow]; rfl
      refine ⟨_, SymAlg.impl_step_tau_snap ids π hpend hact', ?_⟩
      simp only [hS.hπ q hq j hj, hview, inv_smul_smul]
      refine ⟨update_round hS hq hj h1, fun p hp => ?_, fun p => h2 p, ?_⟩
      · dsimp only; rw [Function.update_of_ne (Ne.symm (hp j hj)), h1' p hp]
      · simp [h3])
  refine ⟨D, hD, ⟨fun q' hq' i hi => ?_, fun q' hq' i hi => by rw [hQ2, hC.pend q' hq' i hi],
    fun y => by rw [hQ3, hC.mem]⟩, hQ2⟩
  by_cases hqq : q' = q
  · subst hqq; simp [hQ1 i hi, hi]
  · rw [hQ1' _ (fun j hj => hS.ne_of_group_ne hq hq' hj hi (Ne.symm hqq)), hC.loc q' hq' i hi,
      Function.update_of_ne hqq]

/-- A round in which the members of group `q` return (all with the same response `r`). -/
lemma round_ret {C : A.Cfg} {s : ℕ → S} {b : ℕ → Option O.Op}
    (hC : SymCfg k g e σ sh C s b) {q : ℕ} (hq : q < k) (hb : b q ≠ none) {r : O.Resp} {s' : S}
    (hact : A.act (s q) = .ret r s') :
    ∃ D, (A.impl ids π).runFrom C ((List.range g).map (fun j => .ret (e q j) r)) = some D ∧
      SymCfg k g e σ sh D (Function.update s q s') (Function.update b q none) ∧
      (∀ p, (∀ i < g, e q i ≠ p) → D.pend p = C.pend p) := by
  let Q : ℕ → A.Cfg → Prop := fun j D =>
    (∀ i < g, D.loc (e q i) = if i < j then (σ ^ i) • s' else (σ ^ i) • s q) ∧
    (∀ i < g, D.pend (e q i) = if i < j then none else b q) ∧
    (∀ p, (∀ i < g, e q i ≠ p) → D.loc p = C.loc p ∧ D.pend p = C.pend p) ∧
    D.mem () = C.mem ()
  obtain ⟨D, hD, hQ1, hQ2, hQ3, hQ4⟩ := Impl.runFrom_range (A.impl ids π) Q _ g C
    ⟨fun i hi => by simp [hC.loc q hq i hi], fun i hi => by simp [hC.pend q hq i hi],
      fun _ _ => ⟨rfl, rfl⟩, rfl⟩
    (by
      rintro j hj D ⟨h1, h2, h3, h4⟩
      have hpend : D.pend (e q j) ≠ none := by simpa [h2 j hj] using hb
      have hloc : D.loc (e q j) = (σ ^ j) • s q := by simp [h1 j hj]
      have hact' : A.act (D.loc (e q j)) = .ret r ((σ ^ j) • s') := by
        rw [hloc, hA.act, hact]; rfl
      refine ⟨_, SymAlg.impl_step_ret ids π hpend hact', update_round hS hq hj h1,
        update_round hS hq hj h2, fun p hp => ?_, by simpa using h4⟩
      dsimp only
      rw [Function.update_of_ne (Ne.symm (hp j hj)), Function.update_of_ne (Ne.symm (hp j hj))]
      exact h3 p hp)
  refine ⟨D, hD, ⟨fun q' hq' i hi => ?_, fun q' hq' i hi => ?_, fun y => by rw [hQ4, hC.mem]⟩,
    fun p hp => (hQ3 p hp).2⟩
  · by_cases hqq : q' = q
    · subst hqq; simp [hQ1 i hi, hi]
    · rw [(hQ3 _ (fun j hj => hS.ne_of_group_ne hq hq' hj hi (Ne.symm hqq))).1,
        hC.loc q' hq' i hi, Function.update_of_ne hqq]
  · by_cases hqq : q' = q
    · subst hqq; simp [hQ2 i hi, hi]
    · rw [(hQ3 _ (fun j hj => hS.ne_of_group_ne hq hq' hj hi (Ne.symm hqq))).2,
        hC.pend q' hq' i hi, Function.update_of_ne hqq]

/-- The invocation round of group `q`: all members invoke `o`. -/
lemma round_inv {C : A.Cfg} {s : ℕ → S} {b : ℕ → Option O.Op}
    (hC : SymCfg k g e σ sh C s b) {q : ℕ} (hq : q < k) (hb : b q = none) (o : O.Op) :
    ∃ D, (A.impl ids π).runFrom C ((List.range g).map (fun j => .inv (e q j) o)) = some D ∧
      SymCfg k g e σ sh D (Function.update s q (A.invoke (s q) o))
        (Function.update b q (some o)) ∧
      (∀ p, (∀ i < g, e q i ≠ p) → D.pend p = C.pend p) := by
  let Q : ℕ → A.Cfg → Prop := fun j D =>
    (∀ i < g, D.loc (e q i) =
      if i < j then (σ ^ i) • A.invoke (s q) o else (σ ^ i) • s q) ∧
    (∀ i < g, D.pend (e q i) = if i < j then some o else b q) ∧
    (∀ p, (∀ i < g, e q i ≠ p) → D.loc p = C.loc p ∧ D.pend p = C.pend p) ∧
    D.mem () = C.mem ()
  obtain ⟨D, hD, hQ1, hQ2, hQ3, hQ4⟩ := Impl.runFrom_range (A.impl ids π) Q
    (fun j => Label.inv (e q j) o) g C
    ⟨fun i hi => by simp [hC.loc q hq i hi], fun i hi => by simp [hC.pend q hq i hi],
      fun _ _ => ⟨rfl, rfl⟩, rfl⟩
    (by
      rintro j hj D ⟨h1, h2, h3, h4⟩
      have hpend : D.pend (e q j) = none := by simp [h2 j hj, hb]
      have hloc : A.invoke (D.loc (e q j)) o = (σ ^ j) • A.invoke (s q) o := by
        simp [h1 j hj, hA.invoke]
      refine ⟨_, SymAlg.impl_step_inv (o := o) ids π hpend, ?_, update_round hS hq hj h2,
        fun p hp => ?_, by simpa using h4⟩
      · dsimp only; rw [hloc]; exact update_round hS hq hj h1
      · dsimp only
        rw [Function.update_of_ne (Ne.symm (hp j hj)), Function.update_of_ne (Ne.symm (hp j hj))]
        exact h3 p hp)
  refine ⟨D, hD, ⟨fun q' hq' i hi => ?_, fun q' hq' i hi => ?_, fun y => by rw [hQ4, hC.mem]⟩,
    fun p hp => (hQ3 p hp).2⟩
  · by_cases hqq : q' = q
    · subst hqq; simp [hQ1 i hi, hi]
    · rw [(hQ3 _ (fun j hj => hS.ne_of_group_ne hq hq' hj hi (Ne.symm hqq))).1,
        hC.loc q' hq' i hi, Function.update_of_ne hqq]
  · by_cases hqq : q' = q
    · subst hqq; simp [hQ2 i hi, hi]
    · rw [(hQ3 _ (fun j hj => hS.ne_of_group_ne hq hq' hj hi (Ne.symm hqq))).2,
        hC.pend q' hq' i hi, Function.update_of_ne hqq]

end Rounds

end SymAlg

end Cslib.SharedMemory
