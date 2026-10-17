/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.VC.Defs
public import Cslib.Foundations.Data.Finset.Quorum

/-!
# Vector consensus: one-round facts

Facts about a single round of `VC.algo` in an abstract round execution `E` (any faulty set,
any message loss): the shape of each transition and the genuineness of messages received from
correct processes.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync.VC

open Finset

variable {P VI : Type*} [Fintype P] [DecidableEq P] {t : ℕ} {leader : ℕ → P}
  {F : Finset P} {inp : P → VI} (E : RoundRun (algo (VI := VI) t leader) F inp)

/-! ### Sends -/

theorem send_0 {r : ℕ} (h : r % 5 = 0) (p : P) (s : LState P VI) (q : P) :
    (algo t leader).send r p s q = some (.status s.status) := by
  simp [algo, h]

theorem send_1 {r : ℕ} (h : r % 5 = 1) (p : P) (s : LState P VI) (q : P) :
    (algo t leader).send r p s q = some (.echo s.st0) := by
  simp [algo, h]

theorem send_2 {r : ℕ} (h : r % 5 = 2) (p : P) (s : LState P VI) (q : P) :
    (algo t leader).send r p s q =
      if p = leader (r / 5) then some (.propose (leaderM t s) (leaderS t s)) else none := by
  simp [algo, h]

theorem send_3 {r : ℕ} (h : r % 5 = 3) (p : P) (s : LState P VI) (q : P) :
    (algo t leader).send r p s q = s.cur.map .prepare := by
  simp [algo, h]

theorem send_4 {r : ℕ} (h : r % 5 = 4) (p : P) (s : LState P VI) (q : P) :
    (algo t leader).send r p s q =
      s.prepared.bind fun vm => if vm.1 = r / 5 then some (.commit vm.2) else none := by
  simp [algo, h]

/-! ### Transitions -/

theorem s_succ_0 {r : ℕ} (h : r % 5 = 0) (p : P) :
    E.s (r + 1) p = { E.s r p with st0 := fun j => Msg.getStatus (E.rcv r p j) } := by
  rw [E.s_succ]; simp [algo, h]

theorem s_succ_1 {r : ℕ} (h : r % 5 = 1) (p : P) :
    E.s (r + 1) p = { E.s r p with ech := fun k => Msg.getEcho (E.rcv r p k) } := by
  rw [E.s_succ]; simp [algo, h]

open Classical in
theorem s_succ_2 {r : ℕ} (h : r % 5 = 2) (p : P) :
    E.s (r + 1) p =
      if h : ∃ m S, Msg.getPropose (E.rcv r p (leader (r / 5))) = some (m, S) ∧
          Accept t (E.s r p) S m then
        { E.s r p with cur := some h.choose, acc := (r / 5, h.choose) :: (E.s r p).acc }
      else { E.s r p with cur := none } := by
  rw [E.s_succ]; simp only [algo, h]; simp

open Classical in
theorem s_succ_3 {r : ℕ} (h : r % 5 = 3) (p : P) :
    E.s (r + 1) p =
      if h : ∃ m, Fintype.card P - t ≤ cnt (fun q => E.rcv r p q = some (.prepare m)) then
        { E.s r p with prepared := some (r / 5, h.choose) }
      else E.s r p := by
  rw [E.s_succ]; simp only [algo, h]; simp

open Classical in
theorem s_succ_4 {r : ℕ} (h : r % 5 = 4) (p : P) :
    E.s (r + 1) p =
      if h : (E.s r p).dec = none ∧
          ∃ m, Fintype.card P - t ≤ cnt (fun q => E.rcv r p q = some (.commit m)) then
        { E.s r p with dec := some h.2.choose }
      else E.s r p := by
  rw [E.s_succ]; simp only [algo, h]; simp

/-! ### Field-wise evolution -/

theorem cases_mod5 (r : ℕ) : r % 5 = 0 ∨ r % 5 = 1 ∨ r % 5 = 2 ∨ r % 5 = 3 ∨ r % 5 = 4 := by
  omega

theorem input_succ (r : ℕ) (p : P) : (E.s (r + 1) p).input = (E.s r p).input := by
  rcases cases_mod5 r with h | h | h | h | h
  · rw [s_succ_0 E h]
  · rw [s_succ_1 E h]
  · rw [s_succ_2 E h]; split_ifs <;> rfl
  · rw [s_succ_3 E h]; split_ifs <;> rfl
  · rw [s_succ_4 E h]; split_ifs <;> rfl

theorem input_eq (r : ℕ) (p : P) : (E.s r p).input = inp p := by
  induction r with
  | zero => rw [E.s_zero]; rfl
  | succ r ih => rw [input_succ, ih]

theorem st0_succ {r : ℕ} (h : r % 5 ≠ 0) (p : P) : (E.s (r + 1) p).st0 = (E.s r p).st0 := by
  rcases cases_mod5 r with h' | h' | h' | h' | h'
  · exact absurd h' h
  · rw [s_succ_1 E h']
  · rw [s_succ_2 E h']; split_ifs <;> rfl
  · rw [s_succ_3 E h']; split_ifs <;> rfl
  · rw [s_succ_4 E h']; split_ifs <;> rfl

theorem ech_succ {r : ℕ} (h : r % 5 ≠ 1) (p : P) : (E.s (r + 1) p).ech = (E.s r p).ech := by
  rcases cases_mod5 r with h' | h' | h' | h' | h'
  · rw [s_succ_0 E h']
  · exact absurd h' h
  · rw [s_succ_2 E h']; split_ifs <;> rfl
  · rw [s_succ_3 E h']; split_ifs <;> rfl
  · rw [s_succ_4 E h']; split_ifs <;> rfl

theorem cur_succ {r : ℕ} (h : r % 5 ≠ 2) (p : P) : (E.s (r + 1) p).cur = (E.s r p).cur := by
  rcases cases_mod5 r with h' | h' | h' | h' | h'
  · rw [s_succ_0 E h']
  · rw [s_succ_1 E h']
  · exact absurd h' h
  · rw [s_succ_3 E h']; split_ifs <;> rfl
  · rw [s_succ_4 E h']; split_ifs <;> rfl

theorem prepared_succ (r : ℕ) (p : P) :
    (E.s (r + 1) p).prepared = (E.s r p).prepared ∨
      (r % 5 = 3 ∧ ∃ m, Fintype.card P - t ≤ cnt (fun q => E.rcv r p q = some (.prepare m)) ∧
        (E.s (r + 1) p).prepared = some (r / 5, m)) := by
  rcases cases_mod5 r with h | h | h | h | h
  · left; rw [s_succ_0 E h]
  · left; rw [s_succ_1 E h]
  · left; rw [s_succ_2 E h]; split_ifs <;> rfl
  · rw [s_succ_3 E h]
    split_ifs with hh
    · right; exact ⟨h, hh.choose, hh.choose_spec, rfl⟩
    · left; rfl
  · left; rw [s_succ_4 E h]; split_ifs <;> rfl

theorem acc_succ (r : ℕ) (p : P) :
    (E.s (r + 1) p).acc = (E.s r p).acc ∨
      (r % 5 = 2 ∧ ∃ m, (E.s (r + 1) p).cur = some m ∧
        (E.s (r + 1) p).acc = (r / 5, m) :: (E.s r p).acc) := by
  rcases cases_mod5 r with h | h | h | h | h
  · left; rw [s_succ_0 E h]
  · left; rw [s_succ_1 E h]
  · rw [s_succ_2 E h]
    split_ifs with hh
    · right; exact ⟨h, _, rfl, rfl⟩
    · left; rfl
  · left; rw [s_succ_3 E h]; split_ifs <;> rfl
  · left; rw [s_succ_4 E h]; split_ifs <;> rfl

theorem dec_succ (r : ℕ) (p : P) :
    (E.s (r + 1) p).dec = (E.s r p).dec ∨
      (r % 5 = 4 ∧ (E.s r p).dec = none ∧
        ∃ m, Fintype.card P - t ≤ cnt (fun q => E.rcv r p q = some (.commit m)) ∧
          (E.s (r + 1) p).dec = some m) := by
  rcases cases_mod5 r with h | h | h | h | h
  · left; rw [s_succ_0 E h]
  · left; rw [s_succ_1 E h]
  · left; rw [s_succ_2 E h]; split_ifs <;> rfl
  · left; rw [s_succ_3 E h]; split_ifs <;> rfl
  · rw [s_succ_4 E h]
    split_ifs with hh
    · right; exact ⟨h, hh.1, hh.2.choose, hh.2.choose_spec, rfl⟩
    · left; rfl

/-! ### Index arithmetic -/

theorem mod5 (u : ℕ) {i : ℕ} (hi : i < 5) : (5 * u + i) % 5 = i := by omega

theorem div5 (u : ℕ) {i : ℕ} (hi : i < 5) : (5 * u + i) / 5 = u := by omega

/-! ### Genuineness of messages from correct processes -/

theorem rcv_0 {u : ℕ} {p q : P} (hq : q ∉ F) {msg : Msg P VI}
    (h : E.rcv (5 * u) p q = some msg) : msg = .status (E.s (5 * u) q).status := by
  have := E.honest _ p q msg hq h
  rw [send_0 (by omega)] at this
  exact (Option.some.inj this).symm

theorem rcv_1 {u : ℕ} {p q : P} (hq : q ∉ F) {msg : Msg P VI}
    (h : E.rcv (5 * u + 1) p q = some msg) : msg = .echo (E.s (5 * u + 1) q).st0 := by
  have := E.honest _ p q msg hq h
  rw [send_1 (mod5 u (by omega))] at this
  exact (Option.some.inj this).symm

theorem rcv_2 {u : ℕ} {p q : P} (hq : q ∉ F) {msg : Msg P VI}
    (h : E.rcv (5 * u + 2) p q = some msg) :
    q = leader u ∧
      msg = .propose (leaderM t (E.s (5 * u + 2) q)) (leaderS t (E.s (5 * u + 2) q)) := by
  have := E.honest _ p q msg hq h
  rw [send_2 (mod5 u (by omega)), div5 u (by omega)] at this
  split_ifs at this with hl
  exact ⟨hl, (Option.some.inj this).symm⟩

theorem rcv_3 {u : ℕ} {p q : P} (hq : q ∉ F) {m : Vec P VI}
    (h : E.rcv (5 * u + 3) p q = some (.prepare m)) : (E.s (5 * u + 3) q).cur = some m := by
  have := E.honest _ p q _ hq h
  rw [send_3 (mod5 u (by omega))] at this
  obtain ⟨m', hm', he⟩ := Option.map_eq_some_iff.mp this
  cases he; exact hm'

theorem rcv_4 {u : ℕ} {p q : P} (hq : q ∉ F) {m : Vec P VI}
    (h : E.rcv (5 * u + 4) p q = some (.commit m)) :
    (E.s (5 * u + 4) q).prepared = some (u, m) := by
  have := E.honest _ p q _ hq h
  rw [send_4 (mod5 u (by omega)), div5 u (by omega)] at this
  obtain ⟨⟨v, m'⟩, hm', he⟩ := Option.bind_eq_some_iff.mp this
  simp only at he
  split_ifs at he with hv
  cases he; rw [hm', hv]

/-! ### Multi-round facts -/

omit [Fintype P] [DecidableEq P] in
theorem getStatus_eq_some {x : Option (Msg P VI)} {σ : Status P VI} :
    Msg.getStatus x = some σ ↔ x = some (.status σ) := by
  cases x with
  | none => simp [Msg.getStatus]
  | some y => cases y <;> simp [Msg.getStatus]

omit [Fintype P] [DecidableEq P] in
theorem getEcho_eq_some {x : Option (Msg P VI)} {e : P → Option (Status P VI)} :
    Msg.getEcho x = some e ↔ x = some (.echo e) := by
  cases x with
  | none => simp [Msg.getEcho]
  | some y => cases y <;> simp [Msg.getEcho]

omit [Fintype P] [DecidableEq P] in
theorem getPropose_eq_some {x : Option (Msg P VI)} {m : Vec P VI}
    {S : P → Option (Status P VI)} :
    Msg.getPropose x = some (m, S) ↔ x = some (.propose m S) := by
  cases x with
  | none => simp [Msg.getPropose]
  | some y => cases y <;> simp [Msg.getPropose]

theorem st0_at (u : ℕ) (p : P) :
    (E.s (5 * u + 2) p).st0 = fun j => Msg.getStatus (E.rcv (5 * u) p j) := by
  rw [st0_succ E (by omega), s_succ_0 E (by omega)]

theorem st0_at' (u : ℕ) (p : P) :
    (E.s (5 * u + 1) p).st0 = fun j => Msg.getStatus (E.rcv (5 * u) p j) := by
  rw [s_succ_0 E (by omega)]

theorem ech_at (u : ℕ) (p : P) :
    (E.s (5 * u + 2) p).ech = fun k => Msg.getEcho (E.rcv (5 * u + 1) p k) := by
  rw [s_succ_1 E (mod5 u (by omega))]

omit [DecidableEq P] in
omit [Fintype P] in
/-- Among more than `|F|` processes, one is correct. -/
theorem exists_correct_of_cnt {f : P → Prop} (hF : F.card ≤ t) (h : t + 1 ≤ cnt f) :
    ∃ k, k ∉ F ∧ f k := by
  unfold cnt at h
  have hfin : {q | f q}.Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨k, hk, hkF⟩ := Finset.exists_mem_notMem_of_card_le_of_lt (s := hfin.toFinset) hF
    (by rw [← Set.ncard_eq_toFinset_card _ hfin]; omega)
  exact ⟨k, hkF, by simpa using hk⟩

/-- **Confirmed statuses of correct processes are genuine.** -/
theorem confirmed_genuine (hF : F.card ≤ t) {u : ℕ} {p : P} {S : P → Option (Status P VI)}
    (hS : Confirmed t (E.s (5 * u + 2) p) S) {j : P} (hj : j ∉ F) {σ : Status P VI}
    (hσ : S j = some σ) : σ = (E.s (5 * u) j).status := by
  rcases hS j σ hσ with h | h
  · rw [st0_at E u p, getStatus_eq_some] at h
    have := rcv_0 E hj h
    exact (Msg.status.inj this)
  · obtain ⟨k, hk, e, he, hej⟩ := exists_correct_of_cnt hF h
    rw [ech_at E u p, getEcho_eq_some] at he
    have h1 := rcv_1 E hk he
    cases h1
    rw [st0_at' E u k, getStatus_eq_some] at hej
    exact Msg.status.inj (rcv_0 E hj hej)

/-- A vector accepted in view `u` passed the acceptance test against the leader's message. -/
theorem cur_at {u : ℕ} {p : P} {m : Vec P VI} (h : (E.s (5 * u + 3) p).cur = some m) :
    ∃ S, E.rcv (5 * u + 2) p (leader u) = some (.propose m S) ∧
      Accept t (E.s (5 * u + 2) p) S m := by
  classical
  rw [s_succ_2 E (mod5 u (by omega)), div5 u (by omega)] at h
  split_ifs at h with hh
  · simp only [Option.some.injEq] at h
    obtain ⟨S, hS, hA⟩ := hh.choose_spec
    rw [h] at hS hA
    exact ⟨S, getPropose_eq_some.mp hS, hA⟩

theorem cur_at_4 (u : ℕ) (p : P) : (E.s (5 * u + 4) p).cur = (E.s (5 * u + 3) p).cur :=
  cur_succ E (by omega) p

/-- `prepared` records a prepare quorum of an earlier view. -/
theorem prepared_spec {r : ℕ} {p : P} {v : ℕ} {m : Vec P VI}
    (h : (E.s r p).prepared = some (v, m)) :
    5 * v + 4 ≤ r ∧
      Fintype.card P - t ≤ cnt (fun q => E.rcv (5 * v + 3) p q = some (.prepare m)) := by
  induction r with
  | zero => simp [E.s_zero, algo] at h
  | succ r ih =>
    rcases prepared_succ E r p with h' | ⟨hr, m', hq, h'⟩
    · obtain ⟨h1, h2⟩ := ih (h' ▸ h); exact ⟨by omega, h2⟩
    · rw [h'] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : 5 * (r / 5) + 3 = r := by omega
      rw [this]; exact ⟨by omega, hq⟩

/-- Once prepared, a process stays prepared, at a view that only grows. -/
theorem prepared_mono {r r' : ℕ} {p : P} {v : ℕ} {m : Vec P VI}
    (h : (E.s r p).prepared = some (v, m)) (hr : r ≤ r') :
    ∃ v' m', (E.s r' p).prepared = some (v', m') ∧ v ≤ v' ∧ (v' = v → m' = m) := by
  induction r', hr using Nat.le_induction with
  | base => exact ⟨v, m, h, le_rfl, fun _ => rfl⟩
  | succ r' hr ih =>
    obtain ⟨v', m', h', hv, hm⟩ := ih
    rcases prepared_succ E r' p with h'' | ⟨hr', m'', -, h''⟩
    · exact ⟨v', m', h''.trans h', hv, hm⟩
    · refine ⟨r' / 5, m'', h'', ?_, ?_⟩
      · have := (prepared_spec E h').1; omega
      · intro hv'; have := (prepared_spec E h').1; omega

/-- Accepted pairs come from acceptances. -/
theorem acc_spec {r : ℕ} {q : P} {v : ℕ} {m : Vec P VI} (h : (v, m) ∈ (E.s r q).acc) :
    5 * v + 3 ≤ r ∧ (E.s (5 * v + 3) q).cur = some m := by
  induction r with
  | zero => simp [E.s_zero, algo] at h
  | succ r ih =>
    rcases acc_succ E r q with h' | ⟨hr, m', hc, h'⟩
    · obtain ⟨h1, h2⟩ := ih (h' ▸ h); exact ⟨by omega, h2⟩
    · rw [h'] at h
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have : 5 * (r / 5) + 3 = r + 1 := by omega
        rw [this]; exact ⟨by omega, hc⟩
      · obtain ⟨h1, h2⟩ := ih h; exact ⟨by omega, h2⟩

theorem acc_mono {r r' : ℕ} (hr : r ≤ r') (q : P) : (E.s r q).acc ⊆ (E.s r' q).acc := by
  induction r', hr using Nat.le_induction with
  | base => exact fun _ h => h
  | succ r' hr ih =>
    rcases acc_succ E r' q with h | ⟨-, m, -, h⟩
    · rw [h]; exact ih
    · rw [h]; exact fun x hx => List.mem_cons_of_mem _ (ih hx)

/-- A vector accepted in view `u` is in `acc` from then on. -/
theorem mem_acc_of_cur {u : ℕ} {q : P} {m : Vec P VI} (h : (E.s (5 * u + 3) q).cur = some m)
    {r : ℕ} (hr : 5 * u + 3 ≤ r) : (u, m) ∈ (E.s r q).acc := by
  refine acc_mono E hr q ?_
  rcases acc_succ E (5 * u + 2) q with h' | ⟨-, m', hc, h'⟩
  · exfalso
    have := cur_at E h
    obtain ⟨S, -, -⟩ := this
    -- an acceptance always extends `acc`
    classical
    have h2 := s_succ_2 E (r := 5 * u + 2) (mod5 u (by omega)) q
    rw [div5 u (by omega)] at h2
    split_ifs at h2 with hh
    · rw [h2] at h'
      exact List.cons_ne_self _ _ h'
    · rw [h2] at h; simp at h
  · rw [h, Option.some.injEq] at hc
    rw [h', div5 u (by omega), hc]; exact List.mem_cons_self

/-- Decisions come from commit quorums. -/
theorem dec_spec {r : ℕ} {p : P} {m : Vec P VI} (h : (E.s r p).dec = some m) :
    ∃ u, 5 * u + 5 ≤ r ∧
      Fintype.card P - t ≤ cnt (fun q => E.rcv (5 * u + 4) p q = some (.commit m)) := by
  induction r with
  | zero => simp [E.s_zero, algo] at h
  | succ r ih =>
    rcases dec_succ E r p with h' | ⟨hr, -, m', hq, h'⟩
    · obtain ⟨u, h1, h2⟩ := ih (h' ▸ h); exact ⟨u, by omega, h2⟩
    · rw [h'] at h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨r / 5, by omega, ?_⟩
      have : 5 * (r / 5) + 4 = r := by omega
      rw [this]; exact hq

theorem dec_mono {r r' : ℕ} {p : P} {m : Vec P VI} (h : (E.s r p).dec = some m) (hr : r ≤ r') :
    (E.s r' p).dec = some m := by
  induction r', hr using Nat.le_induction with
  | base => exact h
  | succ r' hr ih =>
    rcases dec_succ E r' p with h' | ⟨-, hn, -⟩
    · rw [h', ih]
    · rw [ih] at hn; simp at hn

end Cslib.Byzantine.PartialSync.VC
