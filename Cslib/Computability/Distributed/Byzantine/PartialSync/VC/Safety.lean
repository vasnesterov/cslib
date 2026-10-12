/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.VC.Quorum

/-!
# Vector consensus: safety

Agreement and vector validity hold in every round execution with at most `t < n / 3` faulty
processes, whatever messages are lost.

The key invariant (`cur_eq_of_commitQ`): once a commit quorum for `m` formed in view `w`
(`n - t - |F|` correct processes prepared `(w, m)`), no correct process accepts a vector other
than `m` in a later view. The proof is PBFT's: the evidence `S` of a later proposal must contain
a (genuine, thanks to echoing) status of a process of the commit quorum, which reports a prepared
pair `(v', m)` with `v' ≥ w`; this rules out a fresh proposal and forces the "locked" view `v` of
another vector to exceed `w`, and then one of the `t + 1` processes vouching for it is correct
and accepted it in a view in `(w, u)`, contradicting the induction hypothesis.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync.VC

open Finset

variable {P VI : Type*} [Fintype P] [DecidableEq P] {t : ℕ} {leader : ℕ → P}
  {F : Finset P} {inp : P → VI} (E : RoundRun (algo (VI := VI) t leader) F inp)

/-- A commit quorum for `m` in view `w`. -/
def CommitQ (w : ℕ) (m : Vec P VI) : Prop :=
  Fintype.card P - t - F.card ≤
    cnt (fun q => q ∉ F ∧ (E.s (5 * w + 4) q).prepared = some (w, m))

/-- **Key invariant.** After a commit quorum for `m` in view `w`, correct processes accept only
`m` in later views. -/
theorem cur_eq_of_commitQ (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) {w : ℕ}
    {m : Vec P VI} (hC : CommitQ E w m) :
    ∀ u, w < u → ∀ q ∉ F, ∀ m', (E.s (5 * u + 3) q).cur = some m' → m' = m := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hwu q hq m' hcur
    obtain ⟨S, -, hconf, hjust⟩ := cur_at E hcur
    -- members of the commit quorum report a prepared pair `(v', m)` with `w ≤ v' < u`
    have hmem : ∀ c, c ∉ F → (E.s (5 * w + 4) c).prepared = some (w, m) →
        ∃ v', w ≤ v' ∧ v' < u ∧ (E.s (5 * u) c).prepared = some (v', m) := by
      intro c hc hpc
      obtain ⟨v', m'', h1, h2, h3⟩ := prepared_mono E hpc (show 5 * w + 4 ≤ 5 * u by omega)
      have hv'u := (prepared_spec E h1).1
      refine ⟨v', h2, by omega, ?_⟩
      rw [h1]
      rcases Nat.eq_or_lt_of_le h2 with h | h
      · rw [h3 h.symm]
      · -- a later prepare quorum: by induction it is for `m`
        have hq' := prepQ_of_prepared E h1
        unfold PrepQ at hq'
        obtain ⟨k, hk, hkc⟩ : ∃ k, k ∉ F ∧ (E.s (5 * v' + 3) k).cur = some m'' :=
          exists_of_cnt_pos (f := fun q => q ∉ F ∧ (E.s (5 * v' + 3) q).cur = some m'') (by omega)
        rw [ih v' (by omega) h k hk m'' hkc]
    -- genuine statuses of quorum members are in every large subset of `S`
    have hgen : ∀ (f : P → Prop), Fintype.card P - t ≤ cnt f →
        ∃ c, f c ∧ c ∉ F ∧ ∃ v', w ≤ v' ∧ v' < u ∧ (E.s (5 * u) c).prepared = some (v', m) := by
      intro f hf
      have hlt : Fintype.card P < cnt f +
          cnt (fun q => q ∉ F ∧ (E.s (5 * w + 4) q).prepared = some (w, m)) := by
        unfold CommitQ at hC; omega
      obtain ⟨c, hfc, hc, hpc⟩ := exists_of_cnt_add hlt
      exact ⟨c, hfc, hc, hmem c hc hpc⟩
    rcases hjust with ⟨hfresh, -, -⟩ | ⟨v, hA1, hA2⟩
    · -- a fresh proposal is impossible
      obtain ⟨c, ⟨σ, hσ, hnone⟩, hc, v', -, -, hpc⟩ := hgen _ hfresh
      have := confirmed_genuine E hF hconf hc hσ
      rw [this] at hnone
      simp [LState.status, hpc] at hnone
    · by_contra hne
      obtain ⟨c, ⟨σ, hσ, hA⟩, hc, v', hwv', -, hpc⟩ := hgen _ hA1
      have hσc := confirmed_genuine E hF hconf hc hσ
      have := hA v' m (by rw [hσc]; exact hpc)
      have hvv : v' < v := by
        rcases this with h | ⟨-, h⟩
        · exact h
        · exact absurd h.symm hne
      -- one of the `t + 1` vouching statuses is correct
      obtain ⟨k, hk, σk, hσk, v'', hvv'', hacc⟩ := exists_correct_of_cnt hF hA2
      rw [confirmed_genuine E hF hconf hk hσk] at hacc
      obtain ⟨h1, h2⟩ := acc_spec E hacc
      exact hne (ih v'' (by omega) (by omega) k hk m' h2)

/-- After a commit quorum for `m` in view `w`, every prepare quorum of a view `≥ w` is for `m`. -/
theorem prepQ_eq_of_commitQ (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) {w : ℕ}
    {m : Vec P VI} (hC : CommitQ E w m) {u : ℕ} (hu : w ≤ u) {m' : Vec P VI}
    (h : PrepQ E u m') : m' = m := by
  have hpos : 0 < Fintype.card P - t - F.card := by omega
  rcases Nat.eq_or_lt_of_le hu with rfl | hlt
  · obtain ⟨c, hc, hpc⟩ : ∃ c, c ∉ F ∧ (E.s (5 * w + 4) c).prepared = some (w, m) :=
      exists_of_cnt_pos (f := fun q => q ∉ F ∧ (E.s (5 * w + 4) q).prepared = some (w, m))
        (by unfold CommitQ at hC; omega)
    exact prepQ_unique E hn hF h (prepQ_of_prepared E hpc)
  · obtain ⟨k, hk, hkc⟩ : ∃ k, k ∉ F ∧ (E.s (5 * u + 3) k).cur = some m' :=
      exists_of_cnt_pos (f := fun q => q ∉ F ∧ (E.s (5 * u + 3) q).cur = some m')
        (by unfold PrepQ at h; omega)
    exact cur_eq_of_commitQ E hn hF hC u hlt k hk m' hkc

/-- A decision is backed by a commit quorum and a prepare quorum of the same view. -/
theorem quorums_of_dec (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) {r : ℕ} {p : P}
    {m : Vec P VI} (h : (E.s r p).dec = some m) : ∃ w, CommitQ E w m ∧ PrepQ E w m := by
  obtain ⟨w, -, hq⟩ := commit_quorum_of_dec E h
  refine ⟨w, hq, ?_⟩
  obtain ⟨c, hc, hpc⟩ : ∃ c, c ∉ F ∧ (E.s (5 * w + 4) c).prepared = some (w, m) :=
    exists_of_cnt_pos (f := fun q => q ∉ F ∧ (E.s (5 * w + 4) q).prepared = some (w, m)) (by omega)
  exact prepQ_of_prepared E hpc

/-- **Agreement** (among all processes that decide, in fact). -/
theorem agreement (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) {r r' : ℕ} {p q : P}
    {m m' : Vec P VI} (h : (E.s r p).dec = some m) (h' : (E.s r' q).dec = some m') : m = m' := by
  obtain ⟨w, hC, hP⟩ := quorums_of_dec E hn hF h
  obtain ⟨w', hC', hP'⟩ := quorums_of_dec E hn hF h'
  rcases le_total w w' with hle | hle
  · exact (prepQ_eq_of_commitQ E hn hF hC hle hP').symm
  · exact prepQ_eq_of_commitQ E hn hF hC' hle hP

/-- Accepted vectors are valid: `n - t` entries, genuine for correct processes. -/
theorem cur_valid (hF : F.card ≤ t) :
    ∀ u, ∀ q ∉ F, ∀ m, (E.s (5 * u + 3) q).cur = some m →
      m.procs.card = Fintype.card P - t ∧ ∀ j ∉ F, m j ≠ none → m j = some (inp j) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro q hq m hcur
    obtain ⟨S, -, hconf, hjust⟩ := cur_at E hcur
    rcases hjust with ⟨-, hcard, hin⟩ | ⟨v, -, hA2⟩
    · refine ⟨hcard, fun j hj hmj => ?_⟩
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hmj
      obtain ⟨σ, hσ, hσx⟩ := hin j x hx
      rw [confirmed_genuine E hF hconf hj hσ] at hσx
      rw [hx, ← hσx]
      simp [LState.status, input_eq]
    · obtain ⟨k, hk, σk, hσk, v'', -, hacc⟩ := exists_correct_of_cnt hF hA2
      rw [confirmed_genuine E hF hconf hk hσk] at hacc
      obtain ⟨h1, h2⟩ := acc_spec E hacc
      exact ih v'' (by omega) k hk m h2

/-- **Vector validity.** -/
theorem dec_valid (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) {r : ℕ} {p : P}
    {m : Vec P VI} (h : (E.s r p).dec = some m) :
    m.procs.card = Fintype.card P - t ∧ ∀ j ∉ F, m j ≠ none → m j = some (inp j) := by
  obtain ⟨w, -, hP⟩ := quorums_of_dec E hn hF h
  obtain ⟨k, hk, hkc⟩ : ∃ k, k ∉ F ∧ (E.s (5 * w + 3) k).cur = some m :=
    exists_of_cnt_pos (f := fun q => q ∉ F ∧ (E.s (5 * w + 3) q).cur = some m)
      (by unfold PrepQ at hP; omega)
  exact cur_valid E hF w k hk m hkc

end Cslib.Byzantine.PartialSync.VC
