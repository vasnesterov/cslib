/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Consensus

/-!
# Round-based algorithms on top of the partially synchronous model

The *basic round model* of Dwork–Lynch–Stockmeyer: rounds of `L` time units (`L ≥ δ + 1`).
In round `r` (times `[r L, r L + L)`), every process sends its round-`r` messages at time `r L`,
collects the round-`r` messages delivered during the round (messages are tagged with their round;
late messages are discarded) and applies its round transition at the end of the round.

* `RoundAlgorithm`: a round-based algorithm (one optional message per receiver and round).
* `RoundAlgorithm.compile RA L`: the corresponding `Algorithm` of the time-based model.
* `RoundRun RA F inp`: an abstract execution of a round algorithm: states `s r p` at the beginning
  of round `r` and received messages `rcv r p q`; messages from correct senders are genuine
  (`honest`), but may be lost; `SyncFrom r₀`: from round `r₀` on no message between correct
  processes is lost.
* `Run.toRoundRun`: every run of the compiled algorithm induces a `RoundRun`
  (`Run.toRoundRun_syncFrom`: synchronous from the first round starting after GST), and
  decisions correspond (`Run.decides_compile_iff`).
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

variable {P Msg S VI VO : Type*} [DecidableEq P]

/-- A round-based algorithm. `send r p s q`: the round-`r` message of `p` (in state `s`) to `q`;
`trans r p s rcv`: the state of `p` after round `r`, given the round-`r` messages received from
each sender. -/
structure RoundAlgorithm (P Msg S VI VO : Type*) where
  /-- The initial state of a process with a given proposal. -/
  init : P → VI → S
  /-- `send r p s q`: the round-`r` message of `p` in state `s` to `q`, if any. -/
  send : ℕ → P → S → P → Option Msg
  /-- `trans r p s rcv`: the state of `p` after round `r`, given the received messages. -/
  trans : ℕ → P → S → (P → Option Msg) → S
  /-- The decision (if any) exhibited by a state. -/
  decide : P → S → Option VO

/-- Local state of a compiled round algorithm: a clock, the round state, and the buffer of
round-`r` messages received so far in the current round. -/
structure RState (P Msg S : Type*) where
  /-- The number of time steps taken so far. -/
  clock : ℕ
  /-- The state of the round algorithm. -/
  s : S
  /-- The first round-tagged message received from each sender in the current round. -/
  buf : P → Option Msg

namespace RoundAlgorithm

variable (RA : RoundAlgorithm P Msg S VI VO) (L : ℕ)

/-- The buffer after receiving the inbox `ib` at time `st.clock`: the first round-`r`-tagged
message from each sender is kept. -/
def newBuf (st : RState P Msg S) (ib : P → List (ℕ × Msg)) : P → Option Msg :=
  fun q => (st.buf q).or (((ib q).find? fun m => m.1 == st.clock / L).map Prod.snd)

/-- Compilation of a round algorithm with rounds of length `L` into the time-based model. -/
def compile : Algorithm P (ℕ × Msg) (RState P Msg S) VI VO where
  init p v := ⟨0, RA.init p v, fun _ => none⟩
  send p st q :=
    if st.clock % L = 0 then
      ((RA.send (st.clock / L) p st.s q).map fun m => (st.clock / L, m)).toList
    else []
  step p st ib :=
    if st.clock % L = L - 1 then
      ⟨st.clock + 1, RA.trans (st.clock / L) p st.s (newBuf L st ib), fun _ => none⟩
    else ⟨st.clock + 1, st.s, newBuf L st ib⟩
  decide p st := RA.decide p st.s

end RoundAlgorithm

/-- An abstract execution of a round algorithm with faulty set `F` and proposals `inp`. -/
structure RoundRun (RA : RoundAlgorithm P Msg S VI VO) (F : Finset P) (inp : P → VI) where
  /-- State of `p` at the beginning of round `r`. -/
  s : ℕ → P → S
  /-- Round-`r` message received by `p` from `q`. -/
  rcv : ℕ → P → P → Option Msg
  s_zero : ∀ p, s 0 p = RA.init p (inp p)
  s_succ : ∀ r p, s (r + 1) p = RA.trans r p (s r p) (rcv r p)
  /-- Messages from correct processes are genuine (but may be lost). -/
  honest : ∀ r p q m, q ∉ F → rcv r p q = some m → RA.send r q (s r q) p = some m

/-- From round `r₀` on, no message between correct processes is lost. -/
def RoundRun.SyncFrom {RA : RoundAlgorithm P Msg S VI VO} {F : Finset P} {inp : P → VI}
    (E : RoundRun RA F inp) (r₀ : ℕ) : Prop :=
  ∀ r ≥ r₀, ∀ p q, p ∉ F → q ∉ F → E.rcv r p q = RA.send r q (E.s r q) p

namespace Run

variable {RA : RoundAlgorithm P Msg S VI VO} {L : ℕ} (R : Run P (ℕ × Msg) VI)

private theorem mul_add_mod_of_lt {r L i : ℕ} (hi : i < L) : (r * L + i) % L = i := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

private theorem mul_add_div_of_lt {r L i : ℕ} (hi : i < L) : (r * L + i) / L = r := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]

omit [DecidableEq P] in
theorem compile_step (p : P) (st : RState P Msg S) (ib : P → List (ℕ × Msg)) :
    (RA.compile L).step p st ib =
      if st.clock % L = L - 1 then
        ⟨st.clock + 1, RA.trans (st.clock / L) p st.s (RoundAlgorithm.newBuf L st ib),
          fun _ => none⟩
      else ⟨st.clock + 1, st.s, RoundAlgorithm.newBuf L st ib⟩ := rfl

omit [DecidableEq P] in
theorem compile_send (p : P) (st : RState P Msg S) (q : P) :
    (RA.compile L).send p st q =
      if st.clock % L = 0 then
        ((RA.send (st.clock / L) p st.s q).map fun m => (st.clock / L, m)).toList
      else [] := rfl

/-- The clock of the compiled algorithm is the global time. -/
theorem clock_st_compile (τ : ℕ) (p : P) : (R.st (RA.compile L) τ p).clock = τ := by
  induction τ with
  | zero => rfl
  | succ τ ih =>
    rw [st_succ, compile_step]
    split_ifs <;> simp [ih]

theorem st_succ_compile (τ : ℕ) (p : P) :
    R.st (RA.compile L) (τ + 1) p =
      if τ % L = L - 1 then
        ⟨τ + 1, RA.trans (τ / L) p (R.st (RA.compile L) τ p).s
          (RoundAlgorithm.newBuf L (R.st (RA.compile L) τ p) (R.inbox (RA.compile L) p τ)),
          fun _ => none⟩
      else ⟨τ + 1, (R.st (RA.compile L) τ p).s,
          RoundAlgorithm.newBuf L (R.st (RA.compile L) τ p) (R.inbox (RA.compile L) p τ)⟩ := by
  rw [st_succ, compile_step, clock_st_compile]

/-- Within a round the round state does not change. -/
theorem s_st_compile_round (r : ℕ) {i : ℕ} (hi : i < L) (p : P) :
    (R.st (RA.compile L) (r * L + i) p).s = (R.st (RA.compile L) (r * L) p).s := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [← Nat.add_assoc, st_succ_compile,
      ite_eq_right (by rw [mul_add_mod_of_lt (by omega)]; omega)]
    exact ih (by omega)

theorem s_st_compile_div (hL : 0 < L) (τ : ℕ) (p : P) :
    (R.st (RA.compile L) τ p).s = (R.st (RA.compile L) (τ / L * L) p).s := by
  conv_lhs => rw [← Nat.div_add_mod' τ L]
  exact R.s_st_compile_round _ (Nat.mod_lt _ hL) p

theorem s_st_compile_succ_round (hL : 0 < L) (r : ℕ) (p : P) :
    (R.st (RA.compile L) ((r + 1) * L) p).s =
      RA.trans r p (R.st (RA.compile L) (r * L) p).s
        (RoundAlgorithm.newBuf L (R.st (RA.compile L) (r * L + (L - 1)) p)
          (R.inbox (RA.compile L) p (r * L + (L - 1)))) := by
  have h : (r + 1) * L = (r * L + (L - 1)) + 1 := by rw [Nat.succ_mul]; omega
  rw [h, st_succ_compile, ite_eq_left (mul_add_mod_of_lt (by omega))]
  change RA.trans ((r * L + (L - 1)) / L) p (R.st (RA.compile L) (r * L + (L - 1)) p).s _ = _
  rw [mul_add_div_of_lt (by omega), R.s_st_compile_round r (by omega)]

/-- A tagged message from a correct sender was sent at the beginning of the round of its tag. -/
theorem send_of_mem_inbox_compile {p q : P} (hq : q ∉ R.faulty) {τ r : ℕ} {m : Msg}
    (h : (r, m) ∈ R.inbox (RA.compile L) p τ q) :
    RA.send r q (R.st (RA.compile L) (r * L) q).s p = some m := by
  rw [inbox_eq_flatMap, List.mem_flatMap] at h
  obtain ⟨σ, -, hm⟩ := h
  simp only [dlv] at hm
  split_ifs at hm
  swap; · simp at hm
  rw [out_of_correct _ _ hq] at hm
  rw [compile_send, clock_st_compile] at hm
  split_ifs at hm with h0
  swap; · simp at hm
  simp only [Option.mem_toList, Option.map_eq_some_iff, Prod.mk.injEq] at hm
  obtain ⟨m', hs, rfl, rfl⟩ := hm
  have : σ / L * L = σ := by have := Nat.div_add_mod' σ L; omega
  rwa [this]

omit [DecidableEq P] in
theorem newBuf_cases {st : RState P Msg S} {ib : P → List (ℕ × Msg)} {q : P} {m : Msg}
    (h : RoundAlgorithm.newBuf L st ib q = some m) :
    st.buf q = some m ∨ (st.clock / L, m) ∈ ib q := by
  unfold RoundAlgorithm.newBuf at h
  cases hb : st.buf q with
  | some m' => rw [hb] at h; exact Or.inl h
  | none =>
    rw [hb, Option.none_or, Option.map_eq_some_iff] at h
    obtain ⟨⟨r, m'⟩, hf, rfl⟩ := h
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    simp only [beq_iff_eq] at h1
    subst h1
    exact Or.inr h2

/-- Buffered messages from correct senders are genuine. -/
theorem newBuf_compile_spec (hL : 0 < L) {p q : P} (hq : q ∉ R.faulty) (τ : ℕ) {m : Msg}
    (h : RoundAlgorithm.newBuf L (R.st (RA.compile L) τ p) (R.inbox (RA.compile L) p τ) q =
      some m) :
    RA.send (τ / L) q (R.st (RA.compile L) (τ / L * L) q).s p = some m := by
  induction τ generalizing m with
  | zero =>
    rcases newBuf_cases h with hb | hi
    · simp [RoundAlgorithm.compile] at hb
    · rw [clock_st_compile] at hi
      exact R.send_of_mem_inbox_compile hq hi
  | succ τ ih =>
    rcases newBuf_cases h with hb | hi
    · rw [st_succ_compile] at hb
      split_ifs at hb with hτ
      have hd : (τ + 1) / L = τ / L := by
        have h1 := Nat.div_add_mod' τ L
        have h2 := Nat.mod_lt τ hL
        rw [show τ + 1 = τ / L * L + (τ % L + 1) by omega, mul_add_div_of_lt (by omega)]
      rw [hd]
      exact ih hb
    · rw [clock_st_compile] at hi
      exact R.send_of_mem_inbox_compile hq hi

/-- The round execution induced by a run of the compiled algorithm. -/
def toRoundRun (RA : RoundAlgorithm P Msg S VI VO) (L : ℕ) (hL : 0 < L) :
    RoundRun RA R.faulty R.inp where
  s r p := (R.st (RA.compile L) (r * L) p).s
  rcv r p := RoundAlgorithm.newBuf L (R.st (RA.compile L) (r * L + (L - 1)) p)
    (R.inbox (RA.compile L) p (r * L + (L - 1)))
  s_zero p := by rw [Nat.zero_mul]; rfl
  s_succ r p := R.s_st_compile_succ_round hL r p
  honest r p q m hq h := by
    have := R.newBuf_compile_spec hL hq _ h
    rwa [mul_add_div_of_lt (by omega)] at this

/-- Once a round-`r` message from `q` is delivered to `p` at time `r L + j`, the buffer of `p` for
`q` is nonempty until the end of round `r`. -/
theorem newBuf_compile_isSome {p q : P} {r j : ℕ} {m : Msg}
    (hm : (r, m) ∈ R.inbox (RA.compile L) p (r * L + j) q) :
    ∀ k, j ≤ k → k < L → (RoundAlgorithm.newBuf L (R.st (RA.compile L) (r * L + k) p)
      (R.inbox (RA.compile L) p (r * L + k)) q).isSome := by
  intro k hjk
  induction k, hjk using Nat.le_induction with
  | base =>
    intro hj
    unfold RoundAlgorithm.newBuf
    rw [Option.isSome_or, Option.isSome_map, clock_st_compile, mul_add_div_of_lt hj]
    have : (List.find? (fun m => m.1 == r) (R.inbox (RA.compile L) p (r * L + j) q)).isSome :=
      List.find?_isSome.mpr ⟨_, hm, by simp⟩
    simp [this]
  | succ k _ ih =>
    intro hk
    have ih := ih (by omega)
    unfold RoundAlgorithm.newBuf
    rw [Option.isSome_or, ← Nat.add_assoc, st_succ_compile,
      ite_eq_right (by rw [mul_add_mod_of_lt (by omega)]; omega)]
    simp [ih]

/-- The induced round execution is synchronous from the first round starting at or after GST,
provided rounds are long enough (`δ + 1 ≤ L`). -/
theorem toRoundRun_syncFrom {t δ : ℕ} (hR : R.Valid t δ) (hL : δ + 1 ≤ L) :
    (R.toRoundRun RA L (by omega)).SyncFrom ((R.gst + L - 1) / L) := by
  intro r hr p q hp hq
  have hL0 : 0 < L := by omega
  have hgst : R.gst ≤ r * L := by
    have := (Nat.div_lt_iff_lt_mul hL0).mp (Nat.lt_succ_of_le hr)
    rw [Nat.succ_mul] at this
    omega
  have h1 := hR.dl_ge q (r * L) p hq hp
  have h2 := hR.dl_le q (r * L) p hq hp
  rw [max_eq_left hgst] at h2
  obtain ⟨j, hj⟩ : ∃ j, R.dl q (r * L) p = r * L + j := ⟨_, (Nat.add_sub_cancel' h1).symm⟩
  have hjL : j < L := by omega
  change RoundAlgorithm.newBuf L (R.st (RA.compile L) (r * L + (L - 1)) p)
    (R.inbox (RA.compile L) p (r * L + (L - 1))) q = RA.send r q (R.st (RA.compile L) (r * L) q).s p
  cases hs : RA.send r q (R.st (RA.compile L) (r * L) q).s p with
  | none =>
    cases hb : RoundAlgorithm.newBuf L (R.st (RA.compile L) (r * L + (L - 1)) p)
      (R.inbox (RA.compile L) p (r * L + (L - 1))) q with
    | none => rfl
    | some m =>
      have := R.newBuf_compile_spec hL0 hq _ hb
      rw [mul_add_div_of_lt (by omega), hs] at this
      exact absurd this (by simp)
  | some m =>
    have hmem : (r, m) ∈ R.inbox (RA.compile L) p (r * L + j) q := by
      rw [inbox_eq_flatMap, List.mem_flatMap]
      refine ⟨r * L, by simp only [List.mem_range]; omega, ?_⟩
      rw [dlv, ite_eq_left hj, out_of_correct _ _ hq, compile_send, clock_st_compile,
        Nat.mul_mod_left, ite_eq_left rfl, Nat.mul_div_cancel _ hL0, hs]
      simp
    have hsome := R.newBuf_compile_isSome hmem (L - 1) (by omega) (by omega)
    obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hsome
    have := R.newBuf_compile_spec hL0 hq _ hm'
    rw [mul_add_div_of_lt (by omega), hs] at this
    rw [hm', this]

/-- Decisions of the compiled algorithm are decisions of the round execution. -/
theorem decides_compile_iff (hL : 0 < L) {p : P} {v : VO} :
    R.Decides (RA.compile L) p v ↔ ∃ r, RA.decide p ((R.toRoundRun RA L hL).s r p) = some v := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨τ / L, ?_⟩
    change RA.decide p (R.st (RA.compile L) (τ / L * L) p).s = some v
    rw [← R.s_st_compile_div hL]
    exact hτ
  · rintro ⟨r, hr⟩
    exact ⟨r * L, hr⟩

end Run

end Cslib.Byzantine.PartialSync
