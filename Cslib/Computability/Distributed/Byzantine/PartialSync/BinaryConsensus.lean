/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Rounds

/-!
# A verified partially synchronous Byzantine binary consensus protocol (`n ≥ 7t + 1`)

A simple deterministic leader-based protocol in the basic round model (`Rounds.lean`), solving
binary consensus with **strong validity** (if all correct processes propose `v`, only `v` can
be decided) against `t` Byzantine processes when `n ≥ 7t + 1`, in partial synchrony.

Phase `k` consists of two rounds:
* round `2k` (*vote*): everybody broadcasts its current value `x`; a process that receives at
  least `n - t` copies of `v` decides `v` (if not decided yet); the received votes are stored;
* round `2k+1` (*leader*): the leader `leader k` broadcasts a value that it received at least
  `3t + 1` times in round `2k` (if any); a process adopts the leader's value `u` iff it received
  `u` at least `2t + 1` times in round `2k`.

Safety (agreement, validity) holds in every execution (any message loss); the invariant is that
once `n - 2t` correct processes hold `v`, no other value can reach `2t + 1` votes, so they keep
`v`. Termination: in the first phase after GST with a correct leader, the leader sees all
`≥ n - t` correct votes, hence (binary values, `n - t ≥ 6t + 1`) some value `u` with `3t + 1`
votes; every correct process then sees `u` at least `2t + 1` times and adopts it, and everybody
decides in the next vote round.

The resilience `n ≥ 7t + 1` is not optimal (`n ≥ 3t + 1` is); this protocol serves to show that
non-trivial validity properties are solvable in the model for `t ≥ 1`.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync.Binary

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Number of senders from which `v` was received. -/
def count (f : P → Option Bool) (v : Bool) : ℕ := (univ.filter fun q => f q = some v).card

/-- Local state: current value, decision, votes received in the last vote round. -/
structure BState (P : Type*) where
  /-- The current value. -/
  x : Bool
  /-- The decision, if any. -/
  dec : Option Bool
  /-- The votes received in the last vote round, by sender. -/
  lastA : P → Option Bool

variable (t : ℕ) (leader : ℕ → P)

/-- The leader's proposal: a value received at least `3t + 1` times in the last vote round. -/
def proposal (s : BState P) : Bool :=
  if 3 * t + 1 ≤ count s.lastA true then true
  else if 3 * t + 1 ≤ count s.lastA false then false else s.x

/-- Decision rule of a vote round: `n - t` identical votes. -/
def decRule (rcv : P → Option Bool) : Option Bool :=
  if Fintype.card P - t ≤ count rcv true then some true
  else if Fintype.card P - t ≤ count rcv false then some false else none

/-- Adopt the leader's value `u` iff it got `2t + 1` votes in the last vote round. -/
def adopt (s : BState P) : Option Bool → BState P
  | some u => if 2 * t + 1 ≤ count s.lastA u then ⟨u, s.dec, s.lastA⟩ else s
  | none => s

/-- The protocol as a round algorithm. -/
def algo : RoundAlgorithm P Bool (BState P) Bool Bool where
  init _ v := ⟨v, none, fun _ => none⟩
  send r p s _ :=
    if r % 2 = 0 then some s.x else if p = leader (r / 2) then some (proposal t s) else none
  trans r _ s rcv :=
    if r % 2 = 0 then ⟨s.x, s.dec.or (decRule t rcv), rcv⟩ else adopt t s (rcv (leader (r / 2)))
  decide _ s := s.dec

variable {t leader} {F : Finset P} {inp : P → Bool} (E : RoundRun (algo t leader) F inp)

/-! ### One-round facts -/

theorem s_even {r : ℕ} (hr : r % 2 = 0) (p : P) :
    E.s (r + 1) p = ⟨(E.s r p).x, (E.s r p).dec.or (decRule t (E.rcv r p)), E.rcv r p⟩ := by
  rw [E.s_succ]; simp [algo, hr]

theorem s_odd {r : ℕ} (hr : r % 2 = 1) (p : P) :
    E.s (r + 1) p = adopt t (E.s r p) (E.rcv r p (leader (r / 2))) := by
  rw [E.s_succ]; simp [algo, hr]

omit [DecidableEq P] in
theorem adopt_dec (s : BState P) (o : Option Bool) : (adopt t s o).dec = s.dec := by
  cases o with
  | none => rfl
  | some u => simp only [adopt]; split_ifs <;> rfl

omit [DecidableEq P] in
theorem adopt_x (s : BState P) (o : Option Bool) :
    (adopt t s o).x = s.x ∨
      ∃ u, o = some u ∧ 2 * t + 1 ≤ count s.lastA u ∧ (adopt t s o).x = u := by
  cases o with
  | none => left; rfl
  | some u =>
    simp only [adopt]
    split_ifs with h
    · right; exact ⟨u, rfl, h, rfl⟩
    · left; rfl

/-- In a vote round, the message received from a correct process is its value. -/
theorem rcv_even_correct {r : ℕ} (hr : r % 2 = 0) {p q : P} (hq : q ∉ F) {w : Bool}
    (h : E.rcv r p q = some w) : (E.s r q).x = w := by
  have := E.honest r p q w hq h
  simpa [algo, hr] using this

/-- Correct processes holding `v` at the beginning of round `r`. -/
def holders (r : ℕ) (v : Bool) : Finset P := univ.filter fun q => q ∉ F ∧ (E.s r q).x = v

/-- In a vote round, `w` is received at most `|holders w| + |F|` times. -/
theorem count_le (hr : r % 2 = 0) (p : P) (w : Bool) :
    count (E.rcv r p) w ≤ (holders E r w).card + F.card := by
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro q hq
  simp only [mem_filter, mem_univ, true_and] at hq
  by_cases hqF : q ∈ F
  · exact mem_union_right _ hqF
  · exact mem_union_left _ (by simp [holders, hqF, rcv_even_correct E hr hqF hq])

theorem card_holders_add (r : ℕ) :
    (holders E r true).card + (holders E r false).card + F.card = Fintype.card P := by
  have h1 : holders E r true ∪ holders E r false ∪ F = univ := by
    ext q; by_cases hq : q ∈ F <;> cases h : (E.s r q).x <;> simp [holders, hq, h]
  have h2 : Disjoint (holders E r true) (holders E r false) := by
    rw [disjoint_left]; intro q h1 h2; simp_all [holders]
  have h3 : Disjoint (holders E r true ∪ holders E r false) F := by
    rw [disjoint_left]; intro q hq
    simp only [holders, mem_union, mem_filter, mem_univ, true_and] at hq
    rcases hq with h | h <;> exact h.1
  rw [← card_union_of_disjoint h2, ← card_union_of_disjoint h3, h1, card_univ]

/-! ### Safety -/

/-- The safety invariant: at least `n - 2t` correct processes hold `v`. -/
def Good (r : ℕ) (v : Bool) : Prop := Fintype.card P - 2 * t ≤ (holders E r v).card

theorem holders_other_le {r : ℕ} {v : Bool} (hg : Good E r v) :
    (holders E r (!v)).card + F.card ≤ 2 * t := by
  have := card_holders_add E r
  unfold Good at hg
  cases v <;> simp at this ⊢ <;> omega

/-- Under the invariant, a vote round gives any other value at most `2t` votes. -/
theorem count_other_le {r : ℕ} (hr : r % 2 = 0) {v : Bool} (hg : Good E r v)
    (p : P) : count (E.rcv r p) (!v) ≤ 2 * t :=
  (count_le E hr p _).trans (holders_other_le E hg)

theorem eq_of_count {r : ℕ} (hr : r % 2 = 0) {v w : Bool} (hg : Good E r v)
    (p : P) (hw : 2 * t + 1 ≤ count (E.rcv r p) w) : w = v := by
  by_contra hne
  have : w = !v := by cases v <;> cases w <;> simp_all
  subst this
  have := count_other_le E hr hg p
  omega

/-- The invariant survives a phase. -/
theorem good_step {r : ℕ} (hr : r % 2 = 0) {v : Bool} (hg : Good E r v) :
    Good E (r + 2) v := by
  unfold Good at hg ⊢
  refine hg.trans (card_le_card fun q hq => ?_)
  simp only [holders, mem_filter, mem_univ, true_and] at hq ⊢
  refine ⟨hq.1, ?_⟩
  have hodd : (r + 1) % 2 = 1 := by omega
  rw [s_odd E hodd]
  rcases adopt_x (t := t) (E.s (r + 1) q) (E.rcv (r + 1) q (leader ((r + 1) / 2))) with
    h | ⟨u, -, hu, h⟩
  · rw [h, s_even E hr]; exact hq.2
  · rw [h]
    rw [s_even E hr] at hu
    exact eq_of_count E hr hg q hu

theorem good_mono {r r' : ℕ} (hr : r % 2 = 0) (hle : r ≤ r') (hr' : r' % 2 = 0) {v : Bool}
    (hg : Good E r v) : Good E r' v := by
  obtain ⟨k, rfl⟩ : ∃ k, r' = r + 2 * k := ⟨(r' - r) / 2, by omega⟩
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    have := good_step E (show (r + 2 * k) % 2 = 0 by omega) (ih (by omega) (by omega))
    simpa [Nat.mul_succ, Nat.add_assoc] using this

omit [DecidableEq P] in
theorem count_of_decRule {rcv : P → Option Bool} {v : Bool} (h : decRule t rcv = some v) :
    Fintype.card P - t ≤ count rcv v := by
  unfold decRule at h
  split_ifs at h with h1 h2 <;> simp_all

/-- A decision comes from a vote round with `n - t` votes. -/
theorem dec_spec {r : ℕ} {p : P} {v : Bool} (h : (E.s r p).dec = some v) :
    ∃ r' < r, r' % 2 = 0 ∧ decRule t (E.rcv r' p) = some v := by
  induction r with
  | zero => simp [E.s_zero, algo] at h
  | succ r ih =>
    rcases Nat.mod_two_eq_zero_or_one r with hr | hr
    · rw [s_even E hr] at h
      cases hd : (E.s r p).dec with
      | none => rw [hd, Option.none_or] at h; exact ⟨r, by omega, hr, h⟩
      | some w =>
        rw [hd, Option.some_or] at h
        obtain ⟨r', h1, h2, h3⟩ := ih (h ▸ hd)
        exact ⟨r', by omega, h2, h3⟩
    · rw [s_odd E hr, adopt_dec] at h
      obtain ⟨r', h1, h2, h3⟩ := ih h
      exact ⟨r', by omega, h2, h3⟩

theorem good_of_decRule (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) {r : ℕ}
    (hr : r % 2 = 0) {p : P} {v : Bool} (h : decRule t (E.rcv r p) = some v) : Good E r v := by
  have h1 := count_of_decRule h
  have h2 := count_le E hr p v
  unfold Good; omega

/-- Two decisions (by any processes) agree. -/
theorem agreement (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) {r₁ r₂ : ℕ} {p q : P}
    {v w : Bool} (h₁ : (E.s r₁ p).dec = some v) (h₂ : (E.s r₂ q).dec = some w) : v = w := by
  obtain ⟨a, -, ha, hda⟩ := dec_spec E h₁
  obtain ⟨b, -, hb, hdb⟩ := dec_spec E h₂
  have key : ∀ {a b : ℕ} {p q : P} {v w : Bool}, a % 2 = 0 → b % 2 = 0 → a ≤ b →
      decRule t (E.rcv a p) = some v → decRule t (E.rcv b q) = some w → w = v := by
    intro a b p q v w ha hb hab hda hdb
    have hg := good_mono E ha hab hb (good_of_decRule E hn hF ha hda)
    exact eq_of_count E hb hg q (by have := count_of_decRule hdb; omega)
  rcases le_total a b with hab | hab
  · exact (key ha hb hab hda hdb).symm
  · exact key hb ha hab hdb hda

/-- Strong validity: if all correct processes propose `v`, only `v` is decided. -/
theorem validity (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) {v : Bool}
    (hv : ∀ q ∉ F, inp q = v) {r : ℕ} {p : P} {w : Bool} (h : (E.s r p).dec = some w) :
    w = v := by
  obtain ⟨a, -, ha, hda⟩ := dec_spec E h
  have hg0 : Good E 0 v := by
    have : holders E 0 v = univ.filter (· ∉ F) := by
      ext q; by_cases hq : q ∈ F <;> simp [holders, E.s_zero, algo, hq, hv]
    unfold Good
    rw [this, filter_not, card_sdiff_of_subset (subset_univ _), card_univ]
    simp; omega
  have hg := good_mono E (by rfl) (Nat.zero_le a) ha hg0
  exact eq_of_count E ha hg p (by have := count_of_decRule hda; omega)

/-! ### Liveness -/

/-- Decisions persist. -/
theorem dec_mono {r : ℕ} {p : P} {v : Bool} (h : (E.s r p).dec = some v) (k : ℕ) :
    (E.s (r + k) p).dec = some v := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [← Nat.add_assoc]
    rcases Nat.mod_two_eq_zero_or_one (r + k) with hr | hr
    · rw [s_even E hr]; simp [ih]
    · rw [s_odd E hr, adopt_dec]; exact ih

/-- If the vote round `r` and leader round `r + 1` are synchronous, the leader of phase
`r / 2` is correct, and `n ≥ 7t + 1`, then all correct processes hold the same value at
round `r + 2`. -/
theorem unanimous_after_good_phase (hn : 7 * t + 1 ≤ Fintype.card P) (hF : F.card ≤ t)
    {r : ℕ} (hr : r % 2 = 0) (hs : E.SyncFrom r) (hℓ : leader (r / 2) ∉ F) :
    ∃ u, ∀ p ∉ F, (E.s (r + 2) p).x = u := by
  set ℓ := leader (r / 2)
  -- the leader receives every correct vote
  have hrcvℓ : ∀ q ∉ F, E.rcv r ℓ q = some (E.s r q).x := by
    intro q hq; rw [hs r le_rfl ℓ q hℓ hq]; simp [algo, hr]
  have hcntℓ : ∀ w, (holders E r w).card ≤ count (E.rcv r ℓ) w := by
    intro w; refine card_le_card fun q hq => ?_
    simp only [holders, mem_filter, mem_univ, true_and] at hq ⊢
    rw [hrcvℓ q hq.1, hq.2]
  have hsum := card_holders_add E r
  -- the leader's proposal `u` got `3t + 1` votes at the leader
  set u := proposal t (E.s (r + 1) ℓ) with hu
  have hlastA : (E.s (r + 1) ℓ).lastA = E.rcv r ℓ := by rw [s_even E hr]
  have hu3 : 3 * t + 1 ≤ count (E.rcv r ℓ) u := by
    have ht := hcntℓ true
    have hf := hcntℓ false
    simp only [hu, proposal, hlastA]
    split_ifs with h1 h2
    · exact h1
    · exact h2
    · omega
  -- hence at least `2t + 1` correct holders of `u`
  have hhold : 2 * t + 1 ≤ (holders E r u).card := by
    have := count_le E hr ℓ u; omega
  refine ⟨u, fun p hp => ?_⟩
  have hodd : (r + 1) % 2 = 1 := by omega
  have hrcvp : E.rcv (r + 1) p ℓ = some u := by
    rw [hs (r + 1) (by omega) p ℓ hp hℓ]
    simp [algo, hodd, show (r + 1) / 2 = r / 2 by omega, ℓ, u]
  rw [s_odd E hodd, show (r + 1) / 2 = r / 2 by omega, hrcvp]
  have hcp : 2 * t + 1 ≤ count (E.s (r + 1) p).lastA u := by
    rw [s_even E hr]
    refine hhold.trans (card_le_card fun q hq => ?_)
    simp only [holders, mem_filter, mem_univ, true_and] at hq ⊢
    rw [hs r le_rfl p q hp hq.1]; simp [algo, hr, hq.2]
  simp [adopt, hcp]

/-- After a synchronous phase with a correct leader, every correct process has decided by the
end of the next vote round. -/
theorem decides_after_good_phase (hn : 7 * t + 1 ≤ Fintype.card P) (hF : F.card ≤ t)
    {r : ℕ} (hr : r % 2 = 0) (hs : E.SyncFrom r) (hℓ : leader (r / 2) ∉ F) (p : P) (hp : p ∉ F) :
    ∃ v, (E.s (r + 3) p).dec = some v := by
  obtain ⟨u, hu⟩ := unanimous_after_good_phase E hn hF hr hs hℓ
  have hr2 : (r + 2) % 2 = 0 := by omega
  have hcnt : Fintype.card P - t ≤ count (E.rcv (r + 2) p) u := by
    have hsum := card_holders_add E (r + 2)
    have : (holders E (r + 2) u).card + F.card = Fintype.card P := by
      have h0 : holders E (r + 2) (!u) = ∅ := by
        ext q; simp only [holders, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨hq, h⟩; rw [hu q hq] at h; cases u <;> simp at h
      cases u <;> simp_all
    have hle : (holders E (r + 2) u).card ≤ count (E.rcv (r + 2) p) u := by
      refine card_le_card fun q hq => ?_
      simp only [holders, mem_filter, mem_univ, true_and] at hq ⊢
      rw [hs (r + 2) (by omega) p q hp hq.1]; simp [algo, hr2, hq.2]
    omega
  rw [s_even E hr2]
  cases hd : (E.s (r + 2) p).dec with
  | some v => exact ⟨v, by simp⟩
  | none =>
    simp only [Option.none_or]
    unfold decRule
    split_ifs with h1 h2
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
    · cases u <;> simp_all

/-! ### The protocol in the partially synchronous model -/

/-- Strong validity: if all processes of `π(c)` propose `v`, only `v` is admissible. -/
def strongValidity : ValidityProperty P Bool Bool :=
  fun c => {w | ∀ v, (∀ p, c p ≠ none → c p = some v) → w = v}

omit [DecidableEq P] in
/-- Strong validity is not trivial. -/
theorem strongValidity_not_trivial :
    ¬ (strongValidity (P := P)).Trivial t := by
  rintro ⟨w, hw⟩
  have hc : ∀ b : Bool, IsInputConfig t (fun _ : P => some b) := fun b => by
    unfold IsInputConfig; simp [Config.procs]
  have h1 := hw _ (hc true) true (fun _ _ => rfl)
  have h2 := hw _ (hc false) false (fun _ _ => rfl)
  rw [h1] at h2; exact Bool.noConfusion h2

/-- A rotating leader: every process leads infinitely many phases. -/
noncomputable def rotLeader (hP : 0 < Fintype.card P) : ℕ → P :=
  fun k => (Fintype.equivFin P).symm ⟨k % Fintype.card P, Nat.mod_lt _ hP⟩

omit [DecidableEq P] in
theorem rotLeader_surj (hP : 0 < Fintype.card P) (p : P) (k₀ : ℕ) :
    ∃ k ≥ k₀, rotLeader hP k = p := by
  refine ⟨Fintype.card P * k₀ + Fintype.equivFin P p, ?_, ?_⟩
  · have := Nat.le_mul_of_pos_left k₀ hP; omega
  · simp only [rotLeader]
    rw [Equiv.symm_apply_eq]
    ext; simp [Nat.mod_eq_of_lt (Fintype.equivFin P p).isLt]

/-- **The protocol solves binary consensus with strong validity** in the partially synchronous
model with at most `t` Byzantine processes, if `n ≥ 7t + 1`, for every `δ`, with rounds of
length `δ + 1` and any leader schedule in which every process leads infinitely often. -/
theorem solvesConsensus (hn : 7 * t + 1 ≤ Fintype.card P)
    (hlead : ∀ p k₀, ∃ k ≥ k₀, leader k = p) (δ : ℕ) :
    SolvesConsensus t δ ((algo t leader).compile (δ + 1)) strongValidity where
  termination R hR p hp := by
    set E := R.toRoundRun (algo t leader) (δ + 1) (by omega)
    have hs := R.toRoundRun_syncFrom (RA := algo t leader) hR (le_refl (δ + 1))
    set r₀ := (R.gst + (δ + 1) - 1) / (δ + 1)
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ ∉ R.faulty := by
      by_contra h
      push Not at h
      have : R.faulty = Finset.univ := Finset.eq_univ_of_forall h
      have := hR.card_faulty
      simp_all
    obtain ⟨k, hk, hkℓ⟩ := hlead ℓ r₀
    have hr : (2 * k) % 2 = 0 := by omega
    have hsync : E.SyncFrom (2 * k) := fun r hr' => hs r (by omega)
    obtain ⟨v, hv⟩ := decides_after_good_phase E hn hR.card_faulty hr hsync
      (by rw [show 2 * k / 2 = k by omega, hkℓ]; exact hℓ) p hp
    exact ⟨v, (R.decides_compile_iff (by omega)).mpr ⟨_, hv⟩⟩
  agreement R hR p _ q _ v w hv hw := by
    obtain ⟨r₁, h₁⟩ := (R.decides_compile_iff (by omega)).mp hv
    obtain ⟨r₂, h₂⟩ := (R.decides_compile_iff (by omega)).mp hw
    exact Binary.agreement _ (by omega) hR.card_faulty h₁ h₂
  validity R hR p _ w hw := by
    obtain ⟨r, h⟩ := (R.decides_compile_iff (by omega)).mp hw
    intro v hv
    refine Binary.validity _ (by omega) hR.card_faulty (fun q hq => ?_) h
    have := hv q (by simp [Run.inputConf, hq])
    simpa [Run.inputConf, hq] using this

/-- **Non-vacuity**: for every `t` and `n ≥ 7t + 1` there is a non-trivial validity property
(binary strong validity) that is solvable in the partially synchronous model. -/
theorem strongValidity_solvable {P : Type} [Fintype P] [DecidableEq P]
    (hn : 7 * t + 1 ≤ Fintype.card P) (δ : ℕ) : (strongValidity (P := P)).Solvable t δ :=
  ⟨ℕ × Bool, RState P Bool (BState P), (algo t (rotLeader (by omega))).compile (δ + 1),
    solvesConsensus hn (rotLeader_surj (by omega)) δ⟩

end Cslib.Byzantine.PartialSync.Binary
