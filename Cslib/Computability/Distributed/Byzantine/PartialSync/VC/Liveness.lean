/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.VC.Quorum

/-!
# Vector consensus: liveness

In a view `u` that is entirely synchronous and has a correct leader, every correct process
decides by the end of the view.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync.VC

open Finset

variable {P VI : Type*} [Fintype P] [DecidableEq P] {t : ℕ} {leader : ℕ → P}
  {F : Finset P} {inp : P → VI} (E : RoundRun (algo (VI := VI) t leader) F inp)


/-! ### Status and echo rounds of a synchronous view -/

section Sync

variable {u : ℕ}

theorem st0_sync' (hs : E.SyncFrom (5 * u)) {k j : P} (hk : k ∉ F) (hj : j ∉ F) :
    (E.s (5 * u + 1) k).st0 j = some (E.s (5 * u) j).status := by
  rw [st0_at' E u k]
  simp only
  rw [hs (5 * u) le_rfl k j hk hj, send_0 (by omega)]
  rfl

theorem st0_sync (hs : E.SyncFrom (5 * u)) {k j : P} (hk : k ∉ F) (hj : j ∉ F) :
    (E.s (5 * u + 2) k).st0 j = some (E.s (5 * u) j).status := by
  rw [st0_at E u k]
  simp only
  rw [hs (5 * u) le_rfl k j hk hj, send_0 (by omega)]
  rfl

theorem ech_sync (hs : E.SyncFrom (5 * u)) {p k : P} (hp : p ∉ F) (hk : k ∉ F) :
    (E.s (5 * u + 2) p).ech k = some (E.s (5 * u + 1) k).st0 := by
  rw [ech_at E u p]
  simp only
  rw [hs (5 * u + 1) (by omega) p k hp hk, send_1 (mod5 u (by omega))]
  rfl

/-- Echoes from correct processes reach a correct `p`. -/
theorem echoCount_ge (hs : E.SyncFrom (5 * u)) {p : P} (hp : p ∉ F) (j : P)
    (σ : Status P VI) :
    cnt (fun k => k ∉ F ∧ (E.s (5 * u + 1) k).st0 j = some σ) ≤
      echoCount (E.s (5 * u + 2) p) j σ :=
  cnt_mono fun _ ⟨hk, h⟩ => ⟨_, ech_sync E hs hp hk, h⟩

/-- Echoes from correct processes are genuine. -/
theorem echoCount_le (p j : P) (σ : Status P VI) :
    echoCount (E.s (5 * u + 2) p) j σ - F.card ≤
      cnt (fun k => k ∉ F ∧ (E.s (5 * u + 1) k).st0 j = some σ) := by
  refine (cnt_correct (F := F) _).trans (cnt_mono ?_)
  rintro k ⟨hk, e, he, hej⟩
  rw [ech_at E u p, getEcho_eq_some] at he
  have := rcv_1 E hk he
  cases this
  exact ⟨hk, hej⟩

theorem leaderS_correct (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    (hs : E.SyncFrom (5 * u)) {ℓ j : P} (hℓ : ℓ ∉ F) (hj : j ∉ F) :
    leaderS t (E.s (5 * u + 2) ℓ) j = some (E.s (5 * u) j).status := by
  have hst := st0_sync E hs hℓ hj
  have hc : 2 * t + 1 ≤ echoCount (E.s (5 * u + 2) ℓ) j (E.s (5 * u) j).status := by
    refine le_trans ?_ (echoCount_ge E hs hℓ j _)
    have h1 := cnt_correct_all (F := F)
    have h2 : cnt (fun k : P => k ∉ F) ≤
        cnt (fun k => k ∉ F ∧ (E.s (5 * u + 1) k).st0 j = some (E.s (5 * u) j).status) :=
      cnt_mono fun k hk => ⟨hk, st0_sync' E hs hk hj⟩
    omega
  have h : ∃ σ, (E.s (5 * u + 2) ℓ).st0 j = some σ ∧
      2 * t + 1 ≤ echoCount (E.s (5 * u + 2) ℓ) j σ := ⟨_, hst, hc⟩
  unfold leaderS
  split_ifs
  exact h.choose_spec.1.symm.trans hst

theorem leaderS_confirmed (hF : F.card ≤ t) (hs : E.SyncFrom (5 * u)) {p : P} (hp : p ∉ F)
    (ℓ : P) : Confirmed t (E.s (5 * u + 2) p) (leaderS t (E.s (5 * u + 2) ℓ)) := by
  intro j σ hσ
  right
  unfold leaderS at hσ
  split_ifs at hσ with h
  have h1 := h.choose_spec.2
  rw [Option.some.inj hσ] at h1
  have h2 := echoCount_le E (u := u) ℓ j σ
  have h3 := echoCount_ge E hs hp j σ
  omega

end Sync

/-- If every correct process's status is in `S`, some vector is justified by `S`. -/
theorem exists_justified (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) {u : ℕ}
    {S : P → Option (Status P VI)} (hS : ∀ j, j ∉ F → S j = some (E.s (5 * u) j).status) :
    ∃ m, Justified t S m := by
  have hall := cnt_correct_all (P := P) (F := F)
  by_cases hp : ∀ j, j ∉ F → (E.s (5 * u) j).prepared = none
  · -- fresh
    have hcard : Fintype.card P - t ≤ (univ.filter (· ∉ F)).card := by
      have : (univ.filter (· ∉ F)) = Fᶜ := by ext; simp
      rw [this, card_compl]; omega
    obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hcard
    refine ⟨fun q => if q ∈ T then some (inp q) else none, Or.inl ⟨?_, ?_, ?_⟩⟩
    · refine le_trans ?_ (cnt_mono (f := fun q => q ∉ F) fun j hj => ⟨_, hS j hj, hp j hj⟩)
      omega
    · rw [← hTc]; congr 1; ext q; simp [Config.procs]
    · intro q x hx
      simp only at hx
      split_ifs at hx with hq
      cases hx
      exact ⟨_, hS q (mem_filter.mp (hT hq)).2, input_eq E _ q⟩
  · -- locked, at the highest view prepared by a correct process
    push Not at hp
    obtain ⟨j₀, hj₀, hj₀p⟩ := hp
    let C := univ.filter (fun j => j ∉ F ∧ (E.s (5 * u) j).prepared ≠ none)
    let f : P → ℕ := fun j => ((E.s (5 * u) j).prepared.map Prod.fst).getD 0
    obtain ⟨c, hcC, hmax⟩ := C.exists_max_image f ⟨j₀, mem_filter.mpr ⟨mem_univ _, hj₀, hj₀p⟩⟩
    obtain ⟨hc, hcp⟩ := (mem_filter.mp hcC).2
    obtain ⟨⟨v, m⟩, hvm⟩ := Option.ne_none_iff_exists'.mp hcp
    have hQ := prepQ_of_prepared E hvm
    refine ⟨m, Or.inr ⟨v, ?_, ?_⟩⟩
    · refine le_trans ?_ (cnt_mono (f := fun q => q ∉ F) fun j hj => ⟨_, hS j hj, ?_⟩)
      · omega
      · intro v' m' h'
        change (E.s (5 * u) j).prepared = some (v', m') at h'
        have hjC : j ∈ C := mem_filter.mpr ⟨mem_univ _, hj, by simp [h']⟩
        have := hmax j hjC
        simp only [f, hvm, h', Option.map_some, Option.getD_some] at this
        rcases this.lt_or_eq with h | h
        · exact Or.inl h
        · subst h
          exact Or.inr ⟨rfl, prepQ_unique E hn hF (prepQ_of_prepared E h') hQ⟩
    · have h1 := (prepared_spec E hvm).1
      unfold PrepQ at hQ
      refine le_trans (by omega) (hQ.trans (cnt_mono fun q hq =>
        ⟨_, hS q hq.1, v, le_rfl, mem_acc_of_cur E hq.2 (by omega)⟩))

/-- **Liveness.** If all rounds from view `u` on are synchronous and the leader of view `u` is
correct, every correct process has decided at the end of view `u`. -/
theorem decides_after_good_view (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) {u : ℕ}
    (hs : E.SyncFrom (5 * u)) (hℓ : leader u ∉ F) (p : P) (hp : p ∉ F) :
    ∃ m, (E.s (5 * u + 5) p).dec = some m := by
  have hall := cnt_correct_all (P := P) (F := F)
  have hSc : ∀ j, j ∉ F → leaderS t (E.s (5 * u + 2) (leader u)) j = some (E.s (5 * u) j).status :=
    fun j hj => leaderS_correct E hn hF hs hℓ hj
  have hJ : Justified t (leaderS t (E.s (5 * u + 2) (leader u)))
      (leaderM t (E.s (5 * u + 2) (leader u))) := by
    obtain ⟨m, hm⟩ := exists_justified E hn hF hSc
    unfold leaderM
    split_ifs with h
    · exact h.choose_spec
    · exact absurd ⟨m, hm⟩ h
  -- propose round
  have hcur : ∀ q, q ∉ F →
      (E.s (5 * u + 3) q).cur = some (leaderM t (E.s (5 * u + 2) (leader u))) := by
    intro q hq
    have hr : E.rcv (5 * u + 2) q (leader u) =
        some (.propose (leaderM t (E.s (5 * u + 2) (leader u)))
          (leaderS t (E.s (5 * u + 2) (leader u)))) := by
      rw [hs _ (by omega) q _ hq hℓ, send_2 (mod5 u (by omega)), div5 u (by omega)]
      simp
    have hex : ∃ m S,
        Msg.getPropose (E.rcv (5 * u + 2) q (leader ((5 * u + 2) / 5))) = some (m, S) ∧
        Accept t (E.s (5 * u + 2) q) S m := by
      rw [div5 u (by omega), hr]
      exact ⟨_, _, rfl, leaderS_confirmed E hF hs hq _, hJ⟩
    rw [show 5 * u + 3 = 5 * u + 2 + 1 from rfl, s_succ_2 E (mod5 u (by omega))]
    have hr' : E.rcv (5 * u + 2) q (leader ((5 * u + 2) / 5)) = some (.propose
        (leaderM t (E.s (5 * u + 2) (leader u))) (leaderS t (E.s (5 * u + 2) (leader u)))) := by
      rw [div5 u (by omega)]; exact hr
    split_ifs
    obtain ⟨S, h1, -⟩ := hex.choose_spec
    have h2 := (congrArg Msg.getPropose hr').symm.trans h1
    simp only [Msg.getPropose, Option.some.injEq, Prod.mk.injEq] at h2
    exact congrArg some h2.1.symm
  -- prepare round
  have hprep : ∀ p, p ∉ F →
      (E.s (5 * u + 4) p).prepared = some (u, leaderM t (E.s (5 * u + 2) (leader u))) := by
    intro p hp
    have hr : ∀ q, q ∉ F → E.rcv (5 * u + 3) p q =
        some (.prepare (leaderM t (E.s (5 * u + 2) (leader u)))) := by
      intro q hq
      rw [hs _ (by omega) p q hp hq, send_3 (mod5 u (by omega)), hcur q hq]
      rfl
    have hc : Fintype.card P - t ≤ cnt (fun q => E.rcv (5 * u + 3) p q =
        some (.prepare (leaderM t (E.s (5 * u + 2) (leader u))))) :=
      le_trans (by omega) (cnt_mono (f := fun q => q ∉ F) hr)
    rw [show 5 * u + 4 = 5 * u + 3 + 1 from rfl, s_succ_3 E (mod5 u (by omega))]
    split_ifs with h
    · obtain ⟨k, hk, hk'⟩ := exists_correct_of_cnt hF (le_trans (by omega) h.choose_spec)
      have := (rcv_3 E hk hk').symm.trans (hcur k hk)
      rw [div5 u (by omega), Option.some.inj this]
    · exact absurd ⟨_, hc⟩ h
  -- commit round
  have hr : ∀ q, q ∉ F → E.rcv (5 * u + 4) p q =
      some (.commit (leaderM t (E.s (5 * u + 2) (leader u)))) := by
    intro q hq
    rw [hs _ (by omega) p q hp hq, send_4 (mod5 u (by omega)), div5 u (by omega), hprep q hq]
    simp
  have hc : Fintype.card P - t ≤ cnt (fun q => E.rcv (5 * u + 4) p q =
      some (.commit (leaderM t (E.s (5 * u + 2) (leader u))))) :=
    le_trans (by omega) (cnt_mono (f := fun q => q ∉ F) hr)
  rw [show 5 * u + 5 = 5 * u + 4 + 1 from rfl, s_succ_4 E (mod5 u (by omega))]
  split_ifs with h
  · exact ⟨_, rfl⟩
  · exact Option.ne_none_iff_exists'.mp fun hd => h ⟨hd, _, hc⟩

end Cslib.Byzantine.PartialSync.VC
