/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Rounds

/-!
# Sequential composition of round algorithms

`RoundAlgorithm.seq RA₁ k conv RA₂` runs `RA₁` during rounds `0, …, k - 1`; at the end of round
`k - 1` every process `p` starts `RA₂` with input `conv p s₁`, where `s₁` is its final `RA₁`
state, and runs it in rounds `k, k + 1, …` (round `k + r` of the composite is round `r` of
`RA₂`). Messages are tagged with the phase (`M₁ ⊕ M₂`), and messages carrying the wrong tag are
ignored, so Byzantine processes cannot confuse the two phases. Decisions are those of `RA₂`.

For an abstract execution `E : RoundRun (seq RA₁ k conv RA₂) F inp`:
* `E.seqFst : RoundRun RA₁ F inp` agrees with `E` during the first phase (`seqFst_s`, for rounds
  `≤ k`; afterwards `RA₁` keeps running without receiving anything), and is synchronous on
  `[r₀, k)` if `E` is synchronous from `r₀` (`seqFst_rcv_of_syncFrom`);
* `E.seqSnd : RoundRun RA₂ F (fun p => conv p (E.seqFst.s k p))` is the second phase shifted by
  `k` rounds (`s_seq_snd`), synchronous from `r₀ - k` if `E` is synchronous from `r₀`
  (`seqSnd_syncFrom`), and `E` decides exactly what `E.seqSnd` decides (`seq_decide_iff`).

Together with `Run.toRoundRun` (`Cslib.Byzantine.PartialSync.Rounds`), this gives a modular way to
verify multi-phase protocols: verify each phase against `RoundRun`s and compose.

`RoundAlgorithm.mapDecide RA f` post-processes decisions; `RoundRun.unmapDecide` transports
executions back to `RA`.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

variable {P M₁ M₂ S₁ S₂ VI VM VO₁ VO VO' : Type*}

namespace RoundAlgorithm

/-- Post-processing of decisions: `p` decides `w` iff `RA` decides some `v` with `f v = some w`. -/
def mapDecide (RA : RoundAlgorithm P M₁ S₁ VI VO) (f : VO → Option VO') :
    RoundAlgorithm P M₁ S₁ VI VO' :=
  { RA with decide := fun p s => (RA.decide p s).bind f }

/-- **Sequential composition** of round algorithms: `RA₁` during rounds `< k`, then `RA₂` (started
with input `conv p s₁` from the final `RA₁` state `s₁`), messages tagged by phase. The second
component of the state is `none` until `RA₂` starts. -/
def seq (RA₁ : RoundAlgorithm P M₁ S₁ VI VO₁) (k : ℕ) (conv : P → S₁ → VM)
    (RA₂ : RoundAlgorithm P M₂ S₂ VM VO) : RoundAlgorithm P (M₁ ⊕ M₂) (S₁ × Option S₂) VI VO where
  init p v := (RA₁.init p v, if k = 0 then some (RA₂.init p (conv p (RA₁.init p v))) else none)
  send r p s q :=
    if r < k then (RA₁.send r p s.1 q).map Sum.inl
    else (s.2.bind fun s₂ => RA₂.send (r - k) p s₂ q).map Sum.inr
  trans r p s rcv :=
    if r < k then
      (RA₁.trans r p s.1 (fun q => (rcv q).bind Sum.getLeft?),
        if r + 1 = k then
          some (RA₂.init p (conv p (RA₁.trans r p s.1 (fun q => (rcv q).bind Sum.getLeft?))))
        else none)
    else (s.1, s.2.map fun s₂ => RA₂.trans (r - k) p s₂ (fun q => (rcv q).bind Sum.getRight?))
  decide p s := s.2.bind (RA₂.decide p)

end RoundAlgorithm

namespace RoundRun

variable {F : Finset P} {inp : P → VI}

/-- An execution of `RA.mapDecide f` is an execution of `RA` (same states and messages). -/
def unmapDecide {RA : RoundAlgorithm P M₁ S₁ VI VO} {f : VO → Option VO'}
    (E : RoundRun (RA.mapDecide f) F inp) : RoundRun RA F inp where
  s := E.s
  rcv := E.rcv
  s_zero := E.s_zero
  s_succ := E.s_succ
  honest := E.honest

theorem unmapDecide_syncFrom {RA : RoundAlgorithm P M₁ S₁ VI VO} {f : VO → Option VO'}
    {E : RoundRun (RA.mapDecide f) F inp} {r₀ : ℕ} (h : E.SyncFrom r₀) :
    E.unmapDecide.SyncFrom r₀ := h

variable {RA₁ : RoundAlgorithm P M₁ S₁ VI VO₁} {k : ℕ} {conv : P → S₁ → VM}
  {RA₂ : RoundAlgorithm P M₂ S₂ VM VO} (E : RoundRun (RA₁.seq k conv RA₂) F inp)

/-! ### First phase -/

/-- States of the first phase, continued after round `k` without receptions. -/
def seqFstS : ℕ → P → S₁
  | 0, p => RA₁.init p (inp p)
  | r + 1, p => RA₁.trans r p (seqFstS r p)
      (fun q => if r < k then (E.rcv r p q).bind Sum.getLeft? else none)

/-- During the first phase, the first component of the state is the `RA₁` state. -/
theorem seqFstS_eq : ∀ r ≤ k, ∀ p, E.seqFstS r p = (E.s r p).1 := by
  intro r
  induction r with
  | zero => intro _ p; simp [seqFstS, E.s_zero, RoundAlgorithm.seq]
  | succ r ih =>
    intro hr p
    rw [seqFstS, E.s_succ, ih (by omega)]
    simp [RoundAlgorithm.seq, show r < k by omega]

/-- Before round `k`, the second phase has not started. -/
theorem seq_snd_eq_none : ∀ r < k, ∀ p, (E.s r p).2 = none := by
  intro r
  induction r with
  | zero => intro hk p; simp [E.s_zero, RoundAlgorithm.seq, show k ≠ 0 by omega]
  | succ r _ =>
    intro hr p
    rw [E.s_succ]
    simp [RoundAlgorithm.seq, show r < k by omega, show r + 1 ≠ k by omega]

/-- The first phase as an execution of `RA₁` (no receptions after round `k`). -/
def seqFst : RoundRun RA₁ F inp where
  s := E.seqFstS
  rcv r p q := if r < k then (E.rcv r p q).bind Sum.getLeft? else none
  s_zero _ := rfl
  s_succ _ _ := rfl
  honest r p q m hq h := by
    split_ifs at h with hr
    obtain ⟨m', hm', hm⟩ := Option.bind_eq_some_iff.mp h
    cases m' with
    | inr _ => simp at hm
    | inl m'' =>
      simp only [Sum.getLeft?_inl, Option.some.injEq] at hm
      subst hm
      have := E.honest r p q _ hq hm'
      simp only [RoundAlgorithm.seq, hr, ite_true, Option.map_eq_some_iff, Sum.inl.injEq,
        exists_eq_right] at this
      rwa [E.seqFstS_eq r (by omega)]

theorem seqFst_s (r : ℕ) (hr : r ≤ k) (p : P) : E.seqFst.s r p = (E.s r p).1 :=
  E.seqFstS_eq r hr p

/-- If `E` is synchronous from `r₀`, the first phase is synchronous during `[r₀, k)`. -/
theorem seqFst_rcv_of_syncFrom {r₀ : ℕ} (h : E.SyncFrom r₀) {r : ℕ} (hr₀ : r₀ ≤ r) (hr : r < k)
    {p q : P} (hp : p ∉ F) (hq : q ∉ F) :
    E.seqFst.rcv r p q = RA₁.send r q (E.seqFst.s r q) p := by
  change (if r < k then (E.rcv r p q).bind Sum.getLeft? else none) = _
  rw [ite_eq_left_iff.mpr (fun h' => absurd hr h'), h r hr₀ p q hp hq, E.seqFst_s r hr.le]
  simp only [RoundAlgorithm.seq, hr, ite_true]
  cases RA₁.send r q (E.s r q).1 p <;> rfl

/-! ### Second phase -/

/-- The input of the second phase. -/
def seqInp (p : P) : VM := conv p (E.seqFst.s k p)

/-- The `RA₂` state of `p` at round `r` of the second phase. -/
def seqSndS (r : ℕ) (p : P) : S₂ := ((E.s (k + r) p).2).getD (RA₂.init p (E.seqInp p))

/-- At round `k`, `RA₂` starts with input `E.seqInp p`. -/
theorem s_seq_start (p : P) : (E.s k p).2 = some (RA₂.init p (E.seqInp p)) := by
  rw [seqInp, E.seqFst_s k le_rfl]
  rcases k with _ | k
  · simp [E.s_zero, RoundAlgorithm.seq]
  · rw [E.s_succ]
    simp [RoundAlgorithm.seq]

theorem s_seq_snd : ∀ r p, (E.s (k + r) p).2 = some (E.seqSndS r p) := by
  have h0 := E.s_seq_start
  intro r
  induction r with
  | zero => intro p; rw [seqSndS, Nat.add_zero, h0]; rfl
  | succ r ih =>
    intro p
    rw [seqSndS, ← Nat.add_assoc, E.s_succ]
    simp [RoundAlgorithm.seq, ih]

theorem seqSndS_succ (r : ℕ) (p : P) :
    E.seqSndS (r + 1) p =
      RA₂.trans r p (E.seqSndS r p) (fun q => (E.rcv (k + r) p q).bind Sum.getRight?) := by
  have h := E.s_seq_snd (r + 1) p
  rw [← Nat.add_assoc, E.s_succ] at h
  simp only [RoundAlgorithm.seq, show ¬ k + r < k by omega, ite_false, E.s_seq_snd r p,
    Option.map_some, Option.some.injEq, Nat.add_sub_cancel_left] at h
  exact h.symm

/-- The second phase as an execution of `RA₂`, shifted by `k` rounds. -/
def seqSnd : RoundRun RA₂ F E.seqInp where
  s := E.seqSndS
  rcv r p q := (E.rcv (k + r) p q).bind Sum.getRight?
  s_zero p := by
    change ((E.s (k + 0) p).2).getD _ = _
    rw [Nat.add_zero, E.s_seq_start]; rfl
  s_succ r p := E.seqSndS_succ r p
  honest r p q m hq h := by
    obtain ⟨m', hm', hm⟩ := Option.bind_eq_some_iff.mp h
    cases m' with
    | inl _ => simp at hm
    | inr m'' =>
      simp only [Sum.getRight?_inr, Option.some.injEq] at hm
      subst hm
      have := E.honest (k + r) p q _ hq hm'
      simpa [RoundAlgorithm.seq, E.s_seq_snd r q] using this

theorem seqSnd_s (r : ℕ) (p : P) : (E.s (k + r) p).2 = some (E.seqSnd.s r p) :=
  E.s_seq_snd r p

/-- If `E` is synchronous from `r₀`, the second phase is synchronous from `r₀ - k`. -/
theorem seqSnd_syncFrom {r₀ : ℕ} (h : E.SyncFrom r₀) : E.seqSnd.SyncFrom (r₀ - k) := by
  intro r hr p q hp hq
  change (E.rcv (k + r) p q).bind Sum.getRight? = RA₂.send r q (E.seqSndS r q) p
  rw [h (k + r) (by omega) p q hp hq]
  simp only [RoundAlgorithm.seq, show ¬ k + r < k by omega, ite_false, E.s_seq_snd r q,
    Option.bind_some, Nat.add_sub_cancel_left]
  cases RA₂.send r q (E.seqSndS r q) p <;> rfl

/-- The composite decides exactly what the second phase decides. -/
theorem seq_decide_iff {p : P} {v : VO} :
    (∃ r, (RA₁.seq k conv RA₂).decide p (E.s r p) = some v) ↔
      ∃ r, RA₂.decide p (E.seqSnd.s r p) = some v := by
  constructor
  · rintro ⟨r, hr⟩
    by_cases hk : r < k
    · simp [RoundAlgorithm.seq, E.seq_snd_eq_none r hk p] at hr
    · refine ⟨r - k, ?_⟩
      change RA₂.decide p (E.seqSndS (r - k) p) = some v
      have := E.s_seq_snd (r - k) p
      rw [Nat.add_sub_cancel' (by omega)] at this
      simpa [RoundAlgorithm.seq, this] using hr
  · rintro ⟨r, hr⟩
    refine ⟨k + r, ?_⟩
    simp only [RoundAlgorithm.seq, E.s_seq_snd r p, Option.bind_some]
    exact hr

end RoundRun

end Cslib.Byzantine.PartialSync
