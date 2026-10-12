/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.RoundAuth
public import Cslib.Computability.Distributed.Byzantine.PartialSync.Sync

/-!
# Authenticated interactive consistency in synchrony (Dolev–Strong)

Dolev and Strong [DolevStrong1983]: with
unforgeable signatures, Byzantine broadcast — hence interactive consistency — is solvable in
synchrony for **every** number `t` of faults, in `t + 1` rounds.

We verify `n` parallel Dolev–Strong broadcasts (one instance per sender) in the round layer
(`Rounds.lean`) and compile them with rounds of length `δ + 1`; with `gst = 0` every round is
synchronous.

**Protocol** (`alg t`). Tokens are triples `(j, i, v)`: "`j` signs value `v` of instance `i`".
A message is a set of *chains* `(i, v, c)` carrying the tokens `(j, i, v)`, `j ∈ c`. A chain is
*valid in round `r`* (`ChainOK r i c`) if `c` starts with `i` and consists of `r + 1` distinct
signers.
* Initially, `p` has accepted `(p, x_p)` and will send the chain `(p, x_p, [p])`.
* In each round `r ≤ t`, every process sends its pending chains to everybody; at the end of the
  round it accepts every `(i, v)` for which it received a valid chain `(i, v, c)`, and it will
  relay `(i, v, c ++ [p])` in the next round if `p ∉ c`.
* After round `t` (i.e. at the beginning of round `t + 1`), `p` decides the vector whose `i`-th
  entry is some accepted value of instance `i` (chosen by `Classical.epsilon`, a deterministic
  function of the accepted set; no default value is needed).

**Proof.** (1) *Unforgeability at the round level* (`RoundRun.tokens_origin_rcv`): a token of a
correct signer `j` received by a correct process was sent by `j` in an earlier round. (2) If a
correct `j` sends a chain `(i, v, c)` in round `r ≤ t`, it is valid and every correct process
accepts `(i, v)` at the end of round `r` (`spread`). (3) If a correct `p` accepted `(i, v)`
from a chain `c` in round `r'`: if `c` contains a correct signer, (1) + (2) apply; otherwise
`c` has `r' + 1 ≤ t` Byzantine signers, so `r' < t` and `p` relays the chain in round `r' + 1 ≤ t`
(`agree`). Hence correct processes accept the same pairs. (4) For a correct `i`, only `x_i` is ever
accepted for instance `i` (`valid`), by (1).

Main result: `icSolvableAuthSync_dolevStrong`.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

namespace DolevStrong

variable {P VI : Type}

/-- A signature chain `(i, v, c)`: value `v` of instance `i`, signed successively by `c`. -/
abbrev Chain (P VI : Type) := P × VI × List P

/-- A round message: a set of chains. -/
abbrev Msg (P VI : Type) := Set (Chain P VI)

/-- Local state: own proposal, round counter, accepted pairs `(instance, value)`, chains to send
in the next round. -/
structure DSState (P VI : Type) where
  /-- The own proposal. -/
  x : VI
  /-- The round counter. -/
  rd : ℕ
  /-- The accepted pairs `(instance, value)`. -/
  acc : Set (P × VI)
  /-- The chains to send in the next round. -/
  out : Set (Chain P VI)

/-- Signatures: the token `(j, i, v)` is signed by `j`; a message carries the tokens of all its
chains. -/
def auth : Auth P (Msg P VI) (P × P × VI) where
  signer := Prod.fst
  tokens m := {k | ∃ c, (k.2.1, k.2.2, c) ∈ m ∧ k.1 ∈ c}

/-- A chain for instance `i` is valid in round `r` if it starts with `i` and has `r + 1` distinct
signers. -/
def ChainOK (r : ℕ) (i : P) (c : List P) : Prop :=
  c.head? = some i ∧ c.length = r + 1 ∧ c.Nodup

/-- A valid round-`r` chain `(i, v, c)` was received. -/
def Got (r : ℕ) (rcv : P → Option (Msg P VI)) (i : P) (v : VI) (c : List P) : Prop :=
  ∃ q m, rcv q = some m ∧ (i, v, c) ∈ m ∧ ChainOK r i c

/-- The decided vector: for each instance, some accepted value. -/
noncomputable def output (s : DSState P VI) : P → VI :=
  fun i => @Classical.epsilon VI ⟨s.x⟩ (fun v => (i, v) ∈ s.acc)

/-- `n` parallel Dolev–Strong broadcasts, `t + 1` rounds (`0, …, t`). -/
noncomputable def alg (t : ℕ) : RoundAlgorithm P (Msg P VI) (DSState P VI) VI (P → VI) where
  init p x := ⟨x, 0, {(p, x)}, {(p, x, [p])}⟩
  send r _ s _ := if r ≤ t then some s.out else none
  trans r p s rcv :=
    if r ≤ t then
      ⟨s.x, r + 1, s.acc ∪ {iv | ∃ c, Got r rcv iv.1 iv.2 c},
        {ch | ∃ c, Got r rcv ch.1 ch.2.1 c ∧ p ∉ c ∧ ch.2.2 = c ++ [p]}⟩
    else s
  decide _ s := if s.rd = t + 1 then some (output s) else none

section Facts

variable {t : ℕ} {F : Finset P} {inp : P → VI} (E : RoundRun (alg t) F inp)

theorem s_succ_le {r : ℕ} (hr : r ≤ t) (p : P) :
    E.s (r + 1) p = ⟨(E.s r p).x, r + 1,
      (E.s r p).acc ∪ {iv | ∃ c, Got r (E.rcv r p) iv.1 iv.2 c},
      {ch | ∃ c, Got r (E.rcv r p) ch.1 ch.2.1 c ∧ p ∉ c ∧ ch.2.2 = c ++ [p]}⟩ := by
  rw [E.s_succ]
  change (if r ≤ t then _ else _) = _
  simp only [hr, ↓reduceIte]

theorem s_succ_gt {r : ℕ} (hr : t < r) (p : P) : E.s (r + 1) p = E.s r p := by
  rw [E.s_succ]
  change (if r ≤ t then _ else _) = _
  simp only [show ¬ r ≤ t by omega, ↓reduceIte]

theorem s_zero' (p : P) : E.s 0 p = ⟨inp p, 0, {(p, inp p)}, {(p, inp p, [p])}⟩ := E.s_zero p

theorem x_eq (r : ℕ) (p : P) : (E.s r p).x = inp p := by
  induction r with
  | zero => rw [s_zero']
  | succ r ih =>
    rcases Nat.lt_or_ge t r with h | h
    · rw [s_succ_gt E h, ih]
    · rw [s_succ_le E h, ih]

theorem rd_eq {r : ℕ} (hr : r ≤ t + 1) (p : P) : (E.s r p).rd = r := by
  induction r with
  | zero => rw [s_zero']
  | succ r _ => rw [s_succ_le E (by omega)]

theorem s_stable (k : ℕ) (p : P) : E.s (t + 1 + k) p = E.s (t + 1) p := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, s_succ_gt E (by omega), ih]

theorem acc_mono_succ (r : ℕ) (p : P) : (E.s r p).acc ⊆ (E.s (r + 1) p).acc := by
  rcases Nat.lt_or_ge t r with h | h
  · rw [s_succ_gt E h]
  · rw [s_succ_le E h]; exact Set.subset_union_left

theorem acc_mono {r r' : ℕ} (h : r ≤ r') (p : P) : (E.s r p).acc ⊆ (E.s r' p).acc := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ r' _ ih => exact ih.trans (acc_mono_succ E r' p)

theorem acc_init (r : ℕ) (p : P) : (p, inp p) ∈ (E.s r p).acc :=
  acc_mono E (Nat.zero_le r) p (by rw [s_zero']; rfl)

theorem acc_of_got {r : ℕ} (hr : r ≤ t) {p i : P} {v : VI} {c : List P}
    (h : Got r (E.rcv r p) i v c) : (i, v) ∈ (E.s (r + 1) p).acc := by
  rw [s_succ_le E hr]; exact Or.inr ⟨c, h⟩

theorem out_of_got {r : ℕ} (hr : r ≤ t) {p i : P} {v : VI} {c : List P}
    (h : Got r (E.rcv r p) i v c) (hp : p ∉ c) : (i, v, c ++ [p]) ∈ (E.s (r + 1) p).out := by
  rw [s_succ_le E hr]; exact ⟨c, h, hp, rfl⟩

/-- Accepted pairs: the own proposal, or a valid chain received in an earlier round `≤ t`. -/
theorem acc_cases {r : ℕ} {p i : P} {v : VI} (h : (i, v) ∈ (E.s r p).acc) :
    (i = p ∧ v = inp p) ∨ ∃ r' < r, r' ≤ t ∧ ∃ c, Got r' (E.rcv r' p) i v c := by
  induction r with
  | zero =>
    rw [s_zero'] at h
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
    exact Or.inl h
  | succ r ih =>
    rcases Nat.lt_or_ge t r with hr | hr
    · rw [s_succ_gt E hr] at h
      rcases ih h with h' | ⟨r', hr', h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨r', by omega, h'⟩
    · rw [s_succ_le E hr] at h
      rcases h with h | ⟨c, hc⟩
      · rcases ih h with h' | ⟨r', hr', h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨r', by omega, h'⟩
      · exact Or.inr ⟨r, by omega, hr, c, hc⟩

/-- Pending chains are valid for the current round, and their pair is accepted. -/
theorem out_inv {r : ℕ} (hr : r ≤ t + 1) {p i : P} {v : VI} {c : List P}
    (h : (i, v, c) ∈ (E.s r p).out) : ChainOK r i c ∧ (i, v) ∈ (E.s r p).acc := by
  rcases r with _ | r
  · rw [s_zero'] at h ⊢
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨⟨rfl, rfl, List.nodup_singleton _⟩, rfl⟩
  · have hc := h
    rw [s_succ_le E (by omega)] at hc
    obtain ⟨c₀, hg, hp, rfl⟩ := hc
    refine ⟨?_, acc_of_got E (by omega) hg⟩
    obtain ⟨-, -, -, -, ⟨hh, hl, hn⟩⟩ := hg
    refine ⟨?_, by simp [hl], ?_⟩
    · cases c₀ with
      | nil => simp at hl
      | cons a c₀ => simpa using hh
    · rw [List.nodup_append]
      refine ⟨hn, List.nodup_singleton _, fun a ha b hb hab => hp ?_⟩
      rw [List.mem_singleton.mp hb] at hab
      exact hab ▸ ha

/-- Tokens of pending chains are own tokens or tokens received in an earlier round. -/
theorem out_tokens {r : ℕ} {p i j : P} {v : VI} {c : List P} (h : (i, v, c) ∈ (E.s r p).out)
    (hj : j ∈ c) : j = p ∨ ∃ r' < r, ∃ q m, E.rcv r' p q = some m ∧ (j, i, v) ∈ auth.tokens m := by
  induction r generalizing c with
  | zero =>
    rw [s_zero'] at h
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact Or.inl (List.mem_singleton.mp hj)
  | succ r ih =>
    rcases Nat.lt_or_ge t r with hr | hr
    · rw [s_succ_gt E hr] at h
      rcases ih h hj with h' | ⟨r', hr', h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨r', by omega, h'⟩
    · rw [s_succ_le E hr] at h
      obtain ⟨c₀, ⟨q, m, hm, hmem, -⟩, -, rfl⟩ := h
      rcases List.mem_append.mp hj with hj | hj
      · exact Or.inr ⟨r, by omega, q, m, hm, c₀, hmem, hj⟩
      · exact Or.inl (List.mem_singleton.mp hj)

end Facts

/-- The Dolev–Strong round algorithm is unforging. -/
theorem alg_unforging (t : ℕ) : (alg (P := P) (VI := VI) t).Unforging auth := by
  intro F inp E r p q m hm x hx
  have hm' : m = (E.s r p).out := by
    simp only [alg] at hm
    split_ifs at hm
    exact (Option.some.inj hm).symm
  subst hm'
  obtain ⟨c, hc, hj⟩ := hx
  exact out_tokens E hc hj

section Correctness

variable [DecidableEq P] {t : ℕ} {F : Finset P} {inp : P → VI} (E : RoundRun (alg t) F inp)
  (hF : F.card ≤ t) (hsync : E.SyncFrom 0) (hA : E.AuthValid auth)

omit [DecidableEq P] in
include hA in
/-- Unforgeability: a token `(j, i, v)` of a correct `j` received by a correct process in round
`r` comes from a chain `j` sent in a round `≤ min r t`. -/
theorem origin {r : ℕ} {p q j i : P} {v : VI} (hp : p ∉ F) {m : Msg P VI}
    (hm : E.rcv r p q = some m) (hx : (j, i, v) ∈ auth.tokens m) (hj : j ∉ F) :
    ∃ r' ≤ r, r' ≤ t ∧ ∃ c, (i, v, c) ∈ (E.s r' j).out ∧ j ∈ c := by
  obtain ⟨r', hr', w, m', hs, hx'⟩ :=
    E.tokens_origin_rcv (alg_unforging t) hA hp hm hx hj
  change (if r' ≤ t then some (E.s r' j).out else none) = some m' at hs
  split_ifs at hs with hrt
  cases hs
  exact ⟨r', hr', hrt, hx'⟩

omit [DecidableEq P] in
include hsync in
/-- A chain sent by a correct process in round `r ≤ t` makes every correct process accept its
pair at the end of round `r`. -/
theorem spread {r : ℕ} (hr : r ≤ t) {j i : P} {v : VI} {c : List P} (hj : j ∉ F)
    (h : (i, v, c) ∈ (E.s r j).out) {q : P} (hq : q ∉ F) : (i, v) ∈ (E.s (r + 1) q).acc := by
  refine acc_of_got E hr ⟨j, (E.s r j).out, ?_, h, (out_inv E (by omega) h).1⟩
  rw [hsync r (Nat.zero_le _) q j hq hj]
  change (if r ≤ t then _ else _) = _
  simp only [hr, ↓reduceIte]

set_option linter.unusedDecidableInType false in
include hF hsync hA in
/-- **Agreement on accepted pairs.** -/
theorem agree {r : ℕ} {p i : P} {v : VI} (hp : p ∉ F)
    (h : (i, v) ∈ (E.s r p).acc) {q : P} (hq : q ∉ F) : (i, v) ∈ (E.s (t + 1) q).acc := by
  rcases acc_cases E h with ⟨rfl, rfl⟩ | ⟨r', hr', hrt, c, q₀, m, hm, hmem, hok⟩
  · have : (i, inp i, [i]) ∈ (E.s 0 i).out := by rw [s_zero']; rfl
    exact acc_mono E (by omega) q (spread E hsync (Nat.zero_le t) hp this hq)
  · by_cases hc : ∃ j ∈ c, j ∉ F
    · obtain ⟨j, hjc, hj⟩ := hc
      obtain ⟨r'', hr'', hr''t, c', hc', -⟩ := origin E hA hp hm ⟨c, hmem, hjc⟩ hj
      exact acc_mono E (by omega) q (spread E hsync hr''t hj hc' hq)
    · push Not at hc
      have hsub : c.toFinset ⊆ F := fun j hj => hc j (List.mem_toFinset.mp hj)
      have hcard := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hok.2.2, hok.2.1] at hcard
      have hpc : p ∉ c := fun h => hp (hc p h)
      have ho := out_of_got E hrt ⟨q₀, m, hm, hmem, hok⟩ hpc
      exact acc_mono E (by omega) q (spread E hsync (by omega) hp ho hq)

omit [DecidableEq P] in
include hA in
/-- **Validity of accepted pairs.** For a correct `i`, only `inp i` is ever accepted for
instance `i`. -/
theorem valid {i : P} (hi : i ∉ F) (r : ℕ) {p : P} (hp : p ∉ F) {v : VI}
    (h : (i, v) ∈ (E.s r p).acc) : v = inp i := by
  induction r using Nat.strong_induction_on generalizing p v with
  | _ r ih =>
    rcases acc_cases E h with ⟨rfl, rfl⟩ | ⟨r', hr', -, c, q₀, m, hm, hmem, hok⟩
    · rfl
    · have hic : i ∈ c := List.mem_of_mem_head? hok.1
      obtain ⟨r'', hr'', hr''t, c', hc', -⟩ := origin E hA hp hm ⟨c, hmem, hic⟩ hi
      exact ih r'' (by omega) hi (out_inv E (by omega) hc').2

set_option linter.unusedDecidableInType false in
include hF hsync hA in
/-- Correct processes decide the same vector. -/
theorem output_eq {p q : P} (hp : p ∉ F) (hq : q ∉ F) :
    output (E.s (t + 1) p) = output (E.s (t + 1) q) := by
  funext i
  have hset : (fun v => (i, v) ∈ (E.s (t + 1) p).acc) = (fun v => (i, v) ∈ (E.s (t + 1) q).acc) :=
    funext fun v => propext ⟨fun h => agree E hF hsync hA hp h hq,
      fun h => agree E hF hsync hA hq h hp⟩
  simp only [output, hset]

set_option linter.unusedDecidableInType false in
include hF hsync hA in
/-- The decided vector contains the proposals of correct processes. -/
theorem output_valid {p i : P} (hp : p ∉ F) (hi : i ∉ F) : output (E.s (t + 1) p) i = inp i := by
  have hmem : (i, inp i) ∈ (E.s (t + 1) p).acc :=
    agree E hF hsync hA hi (acc_init E 0 i) hp
  exact valid E hA hi _ hp (Classical.epsilon_spec (p := fun v => (i, v) ∈ (E.s (t + 1) p).acc)
    ⟨_, hmem⟩)

omit [DecidableEq P] in
theorem decide_eq {r : ℕ} {p : P} {V : P → VI} (h : (alg t).decide p (E.s r p) = some V) :
    V = output (E.s (t + 1) p) := by
  have hs : E.s r p = E.s (t + 1) p := by
    rcases Nat.lt_or_ge (t + 1) r with hr | hr
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr.le
      exact s_stable E k p
    · change (if (E.s r p).rd = t + 1 then _ else _) = _ at h
      rw [rd_eq E hr] at h
      split_ifs at h with h'
      rw [h']
  rw [hs] at h
  change (if (E.s (t + 1) p).rd = t + 1 then _ else _) = _ at h
  simp only [rd_eq E le_rfl p, ↓reduceIte] at h
  exact (Option.some.inj h).symm

omit [DecidableEq P] in
theorem decide_succ (p : P) : (alg t).decide p (E.s (t + 1) p) = some (output (E.s (t + 1) p)) := by
  change (if (E.s (t + 1) p).rd = t + 1 then _ else _) = _
  simp only [rd_eq E le_rfl p, ↓reduceIte]

end Correctness

end DolevStrong

open DolevStrong in
/-- **Dolev–Strong (1983)**: with signatures, interactive consistency is solvable in synchrony
for every number `t` of Byzantine processes [DolevStrong1983]. The algorithm: `n` parallel
Dolev–Strong broadcasts, compiled with rounds of length `δ + 1`. -/
theorem solvesConsensusAuthSync_dolevStrong {P : Type} [DecidableEq P] {VI : Type}
    (t δ : ℕ) : SolvesConsensusAuthSync (auth (P := P) (VI := VI)).tagged t δ
      ((alg t).compile (δ + 1)) (icValidity P VI) := by
  have hL : 0 < δ + 1 := Nat.succ_pos δ
  have key : ∀ R : Run P (ℕ × Msg P VI) VI, R.Valid t δ →
      R.AuthValid (auth (P := P) (VI := VI)).tagged ((alg t).compile (δ + 1)) → R.gst = 0 →
      (R.toRoundRun (alg t) (δ + 1) hL).SyncFrom 0 := by
    intro R hR _ h0 r _ p q hp hq
    refine R.toRoundRun_syncFrom hR le_rfl r ?_ p q hp hq
    rw [h0, Nat.zero_add, Nat.add_sub_cancel, Nat.div_eq_of_lt (Nat.lt_succ_self δ)]
    exact Nat.zero_le r
  refine ⟨?_, ?_, ?_⟩
  · intro R hR hRa h0 p _
    exact ⟨_, (R.decides_compile_iff hL).mpr ⟨t + 1, decide_succ _ p⟩⟩
  · intro R hR hRa h0 p hp q hq v w hv hw
    obtain ⟨r, hr⟩ := (R.decides_compile_iff hL).mp hv
    obtain ⟨r', hr'⟩ := (R.decides_compile_iff hL).mp hw
    rw [decide_eq _ hr, decide_eq _ hr']
    exact output_eq _ hR.card_faulty (key R hR hRa h0) (R.toRoundRun_authValid hL hRa) hp hq
  · intro R hR hRa h0 p hp v hv
    obtain ⟨r, hr⟩ := (R.decides_compile_iff hL).mp hv
    rw [decide_eq _ hr]
    intro i hi
    have hi' : i ∉ R.faulty := by
      intro h; exact hi (by simp [Run.inputConf, h])
    simp only [Run.inputConf, hi', ite_false]
    rw [output_valid _ hR.card_faulty (key R hR hRa h0) (R.toRoundRun_authValid hL hRa) hp hi']

/-- **Dolev–Strong (1983)**: interactive consistency is authenticated-solvable in synchrony for
every `t < n` [DolevStrong1983].
The bound `t < n` is not needed by the proof. -/
theorem icSolvableAuthSync_dolevStrong {P : Type} [Fintype P] [DecidableEq P] {VI : Type}
    {t δ : ℕ} (_htn : t < Fintype.card P) : (icValidity P VI).SolvableAuthSync t δ :=
  ⟨_, _, _, _, _, RoundAlgorithm.compile_unforging (Nat.succ_pos δ) (DolevStrong.alg_unforging t),
    solvesConsensusAuthSync_dolevStrong t δ⟩

end Cslib.Byzantine.PartialSync
