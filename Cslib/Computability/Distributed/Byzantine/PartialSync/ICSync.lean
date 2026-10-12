/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.RoundSeq
public import Cslib.Computability.Distributed.Byzantine.PartialSync.VC.Main
public import Cslib.Computability.Distributed.Byzantine.PartialSync.Sync

/-!
# Interactive consistency in synchrony for `n > 3t`

Pease, Shostak and Lamport [PeaseShostakLamport1980]: interactive consistency (every correct process
decides the same vector `V` with `V[i]` = the proposal of `p_i` for every correct `p_i`) is solvable
without signatures in synchrony iff `n > 3t`. This file proves the possibility direction in the
shared model (`Cslib.Byzantine.PartialSync`, synchronous runs: `gst = 0`), as used, e.g., in
[CivitEtAl2024].

## Protocol (round algorithm, rounds of length `δ + 1`)

1. **Exchange** (round 0): every process broadcasts its proposal; `p` forms the vector
   `w_p : P → Option VI` of received proposals (its own one at index `p`). In synchrony,
   `w_p i = some x_i` for all correct `p, i`.
2. **Vector consensus** (rounds `≥ 1`) on the vectors `w_p`, with the verified optimal-resilience
   protocol `VC.algo` (`Cslib.Byzantine.PartialSync.VC`): correct processes decide a common
   configuration `D` with `n - t` entries, the entry of each correct `q` being `w_q`.
3. **Output**: for each index `i`, the value occurring at index `i` in strictly more than half
   of the entries of `D` (else a fixed value chosen from `D`). For correct `i`, at least
   `n - 2t` entries are correct and carry `x_i`, and `n - 2t > (n - t) / 2` iff `n > 3t`.

The phases are composed with `RoundAlgorithm.seq` (`Cslib.Byzantine.PartialSync.RoundSeq`).

Main result: `icSolvableSync_of_three_t_lt`.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

namespace IC

variable {P VI : Type*} [Fintype P] [DecidableEq P]

/-- One round of all-to-all exchange of proposals. State: own proposal and the vector of
received proposals. -/
def exchange : RoundAlgorithm P VI (VI × (P → Option VI)) VI Unit where
  init _ v := (v, fun _ => none)
  send _ _ s _ := some s.1
  trans _ p s rcv := (s.1, fun q => if q = p then some s.1 else rcv q)
  decide _ _ := none

omit [Fintype P] in
@[simp] theorem exchange_init (p : P) (v : VI) :
    (exchange (P := P)).init p v = (v, fun _ => none) := rfl
omit [Fintype P] in
@[simp] theorem exchange_send (r : ℕ) (p : P) (s : VI × (P → Option VI)) (q : P) :
    (exchange (P := P)).send r p s q = some s.1 := rfl
omit [Fintype P] in
@[simp] theorem exchange_trans (r : ℕ) (p : P) (s : VI × (P → Option VI)) (rcv : P → Option VI) :
    (exchange (P := P)).trans r p s rcv = (s.1, fun q => if q = p then some s.1 else rcv q) := rfl

/-- Number of entries of `D` whose `i`-th component is `v`. -/
noncomputable def support (D : Config P (P → Option VI)) (i : P) (v : VI) : ℕ :=
  Set.ncard {q | ∃ w, D q = some w ∧ w i = some v}

/-- The output vector computed from a decided configuration of vectors: componentwise strict
majority among the entries of `D`; a fixed value appearing in `D` where there is none. -/
noncomputable def output (D : Config P (P → Option VI)) : Option (P → VI) :=
  open Classical in
  if h : ∃ v : VI, ∃ q w i, D q = some w ∧ w i = some v then
    some (fun i => if h' : ∃ v, D.procs.card < 2 * support D i v then h'.choose else h.choose)
  else none

/-- The interactive consistency protocol: exchange, then vector consensus on the received
vectors, then componentwise majority. -/
noncomputable abbrev algo (t : ℕ) (leader : ℕ → P) :
    RoundAlgorithm P (VI ⊕ VC.Msg P (P → Option VI))
      ((VI × (P → Option VI)) × Option (VC.LState P (P → Option VI))) VI (P → VI) :=
  (exchange (P := P) (VI := VI)).seq 1 (fun _ s => s.2)
    ((VC.algo (VI := P → Option VI) t leader).mapDecide output)

/-! ### Correctness of the output map -/

set_option linter.unusedDecidableInType false in
theorem output_spec {t : ℕ} (hn : 3 * t < Fintype.card P) {F : Finset P} (hF : F.card ≤ t)
    {D : Config P (P → Option VI)} {w : P → P → Option VI} {x : P → VI}
    (hcard : D.procs.card = Fintype.card P - t) (hD : ∀ j ∉ F, D j ≠ none → D j = some (w j))
    (hw : ∀ j ∉ F, ∀ i ∉ F, w j i = some (x i)) :
    ∃ V, output D = some V ∧ ∀ i ∉ F, V i = x i := by
  set C := D.procs \ F with hC
  have hCcard : Fintype.card P - t - t ≤ C.card := by
    have := Finset.le_card_sdiff F D.procs
    rw [hC]; omega
  have hCD : ∀ q ∈ C, D q = some (w q) ∧ q ∉ F := by
    intro q hq
    rw [hC, Finset.mem_sdiff, Config.mem_procs_iff_ne_none] at hq
    exact ⟨hD q hq.2 hq.1, hq.2⟩
  have hsupp : ∀ i ∉ F, C.card ≤ support D i (x i) := by
    intro i hi
    rw [support, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard (fun q hq => ?_) (Set.toFinite _)
    obtain ⟨h1, h2⟩ := hCD q hq
    exact ⟨w q, h1, hw q h2 i hi⟩
  have hex : ∃ v : VI, ∃ q w i, D q = some w ∧ w i = some v := by
    obtain ⟨q, hq⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨h1, h2⟩ := hCD q hq
    exact ⟨x q, q, w q, q, h1, hw q h2 q h2⟩
  -- uniqueness of strict majorities
  have huniq : ∀ i v v', v ≠ v' → support D i v + support D i v' ≤ D.procs.card := by
    intro i v v' hvv'
    rw [support, support, ← Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _),
      ← Set.ncard_coe_finset]
    · refine Set.ncard_le_ncard ?_ (Set.toFinite _)
      rintro q (⟨w', h1, -⟩ | ⟨w', h1, -⟩) <;>
        simp [h1]
    · rw [Set.disjoint_left]
      rintro q ⟨w₁, h1, h2⟩ ⟨w₂, h3, h4⟩
      rw [h1, Option.some.injEq] at h3
      subst h3
      rw [h2, Option.some.injEq] at h4
      exact hvv' h4
  refine ⟨_, by unfold output; rw [dite_eq_left_of_eq_true (eq_true hex)], fun i hi => ?_⟩
  have hmaj : ∃ v, D.procs.card < 2 * support D i v :=
    ⟨x i, by have := hsupp i hi; omega⟩
  simp only [dite_eq_left_of_eq_true (eq_true hmaj)]
  by_contra hne
  have h1 := hmaj.choose_spec
  have h2 := huniq i _ _ hne
  have h3 := hsupp i hi
  omega

/-! ### Correctness of the protocol on round executions -/

section RoundRun

variable {t : ℕ} {leader : ℕ → P} {F : Finset P} {inp : P → VI}
  (E : RoundRun (algo (VI := VI) t leader) F inp)

/-- After the exchange round of a synchronous execution, every correct process holds the
proposal of every correct process. -/
theorem seqInp_eq (hs : E.SyncFrom 0) {q i : P} (hq : q ∉ F) (hi : i ∉ F) :
    E.seqInp q i = some (inp i) := by
  change (E.seqFst.s 1 q).2 i = some (inp i)
  rw [E.seqFst.s_succ]
  by_cases hiq : i = q
  · subst hiq
    simp [E.seqFst.s_zero]
  · simp only [exchange_trans, hiq, ite_false]
    rw [E.seqFst_rcv_of_syncFrom hs le_rfl Nat.zero_lt_one hq hi]
    simp [E.seqFst.s_zero]

/-- The vector consensus execution inside `E`. -/
noncomputable def vcRun : RoundRun (VC.algo (VI := P → Option VI) t leader) F E.seqInp :=
  E.seqSnd.unmapDecide

theorem decide_iff {p : P} {V : P → VI} :
    (∃ r, (algo (VI := VI) t leader).decide p (E.s r p) = some V) ↔
      ∃ r D, ((vcRun E).s r p).dec = some D ∧ output D = some V := by
  rw [E.seq_decide_iff]
  simp only [RoundAlgorithm.mapDecide, Option.bind_eq_some_iff]
  rfl

end RoundRun

/-! ### The compiled protocol solves interactive consistency in synchrony -/

/-- **Interactive consistency is solvable in synchrony for `n > 3t`** (Pease–Shostak–Lamport
1980), for any leader schedule of the inner vector consensus in which every process leads
infinitely many views. -/
theorem solvesConsensusSync {t : ℕ} (hn : 3 * t < Fintype.card P) {leader : ℕ → P}
    (hlead : ∀ p k₀, ∃ k ≥ k₀, leader k = p) (δ : ℕ) :
    SolvesConsensusSync t δ ((algo (VI := VI) t leader).compile (δ + 1)) (icValidity P VI) := by
  -- common setup
  have key : ∀ R : Run P (ℕ × (VI ⊕ VC.Msg P (P → Option VI))) VI, R.Valid t δ → R.gst = 0 →
      (∀ p ∉ R.faulty, ∃ D, ∃ r, ((vcRun (R.toRoundRun (algo t leader) (δ + 1) (by omega))).s r
        p).dec = some D) ∧
      (∀ p q r r' D D', ((vcRun (R.toRoundRun (algo t leader) (δ + 1) (by omega))).s r p).dec =
        some D → ((vcRun (R.toRoundRun (algo t leader) (δ + 1) (by omega))).s r' q).dec =
        some D' → D = D') ∧
      (∀ p r D, ((vcRun (R.toRoundRun (algo t leader) (δ + 1) (by omega))).s r p).dec = some D →
        ∃ V, output D = some V ∧ ∀ i ∉ R.faulty, V i = R.inp i) := by
    intro R hR h0
    set E := R.toRoundRun (algo (VI := VI) t leader) (δ + 1) (by omega)
    have hs : E.SyncFrom 0 := by
      have := R.toRoundRun_syncFrom (RA := algo (VI := VI) t leader) hR (le_refl (δ + 1))
      rwa [h0, Nat.zero_add, Nat.add_sub_cancel, Nat.div_eq_of_lt (by omega)] at this
    have hs₂ : (vcRun E).SyncFrom 0 := by
      have := E.seqSnd_syncFrom hs
      exact RoundRun.unmapDecide_syncFrom this
    have hF := hR.card_faulty
    refine ⟨fun p hp => ?_, fun p q r r' D D' h h' => VC.agreement _ hn hF h h', fun p r D h => ?_⟩
    · obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ ∉ R.faulty := by
        by_contra hc
        push Not at hc
        have : R.faulty = Finset.univ := Finset.eq_univ_of_forall hc
        rw [this, Finset.card_univ] at hF
        omega
      obtain ⟨k, -, hkℓ⟩ := hlead ℓ 0
      obtain ⟨m, hm⟩ := VC.decides_after_good_view (vcRun E) hn hF
        (fun r _ => hs₂ r (Nat.zero_le _)) (hkℓ ▸ hℓ) p hp
      exact ⟨m, _, hm⟩
    · obtain ⟨hcard, hD⟩ := VC.dec_valid _ hn hF h
      exact output_spec hn hF hcard hD fun j hj i hi => seqInp_eq E hs hj hi
  refine ⟨fun R hR _ h0 p hp => ?_, fun R hR _ h0 p hp q hq V W hV hW => ?_,
    fun R hR _ h0 p hp V hV => ?_⟩
  · obtain ⟨D, r, hD⟩ := (key R hR h0).1 p hp
    obtain ⟨V, hV, -⟩ := (key R hR h0).2.2 p r D hD
    exact ⟨V, (R.decides_compile_iff (by omega)).mpr ((decide_iff _).mpr ⟨r, D, hD, hV⟩)⟩
  · obtain ⟨r, D, hD, hDV⟩ := (decide_iff _).mp ((R.decides_compile_iff (by omega)).mp hV)
    obtain ⟨r', D', hD', hDW⟩ := (decide_iff _).mp ((R.decides_compile_iff (by omega)).mp hW)
    obtain rfl := (key R hR h0).2.1 p q r r' D D' hD hD'
    rw [hDV] at hDW
    exact Option.some.inj hDW
  · obtain ⟨r, D, hD, hDV⟩ := (decide_iff _).mp ((R.decides_compile_iff (by omega)).mp hV)
    obtain ⟨V', hV', hval⟩ := (key R hR h0).2.2 p r D hD
    rw [hDV, Option.some.injEq] at hV'
    subst hV'
    intro i hi
    simp only [Run.inputConf] at hi ⊢
    split_ifs at hi ⊢ with hiF
    · exact absurd rfl hi
    · rw [hval i hiF]

end IC

/-- **Interactive consistency is unauthenticated-solvable in synchrony if `n > 3t`**
[PeaseShostakLamport1980]. -/
theorem icSolvableSync_of_three_t_lt {P : Type} [Fintype P] [DecidableEq P] {VI : Type}
    {t δ : ℕ} (hn : 3 * t < Fintype.card P) : (icValidity P VI).SolvableSync t δ :=
  ⟨_, _, (IC.algo (VI := VI) t (Binary.rotLeader (by omega))).compile (δ + 1),
    IC.solvesConsensusSync hn (Binary.rotLeader_surj (by omega)) δ⟩

end Cslib.Byzantine.PartialSync
