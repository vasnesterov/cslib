/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.LockStep.Agreement
import Mathlib.Algebra.Ring.Parity

/-!
# Simulating missing channels by relays

A protocol `alg` designed for a *target* network `G` is compiled into a protocol for an *actual*
network `G'`. Pairs `u, v` with `G.Adj u v ∧ ¬ G'.Adj u v` communicate through a set of relays
`Rel u v` (with `G'.Adj u w ∧ G'.Adj w v` for `w ∈ Rel u v`). One simulated round takes two real
rounds:

* round `2r`: every party sends to all its `G'`-neighbours a *packet* containing its round-`r`
  messages of `alg` for all its `G`-neighbours `d`, each wrapped as `(u, d, r, m)`;
* round `2r+1`: every party forwards to each `G'`-neighbour `v` the components destined to `v` of
  the packets it received in round `2r`;
* `v` decodes the simulated round-`r` inbox: directly from the packet of a `G'`-neighbour, and
  through a *relay rule* `acc` from the forwarded components otherwise.

Two relay rules are provided (as used in [ConstantinescuEtAl2025]):

* `majorityRule` (Lemma 6, unauthenticated): accept `m` if strictly more than half of the relays
  forwarded `m`. If honest parties are a strict majority of every relay set of an honest pair,
  every run of the compiled protocol simulates a reliable run of `alg` (`relay_majority_sim`).
* `sigRule` (Lemmas 8 and 10, authenticated): wrappers `(u, v, r, m)` are signature tokens of `u`
  (`Auth.relay`); accept `m` if some relay forwarded a wrapper `(u, v, r, m)`. Every authenticated
  run of the compiled protocol simulates an authenticated run of `alg` where honest messages are
  only lost between pairs all of whose relays are Byzantine (`relay_sig_sim`).

Compiled decisions are taken at even history lengths only, so first decisions of honest parties
correspond exactly (`decides_relay_iff`), and termination time doubles (`terminatesBy_relay`).

Since honest decisions only are related, the transfer theorems assume that the specification only
depends on the decisions of honest parties (`Spec.HonestOnly`, satisfied by `BB`, `BA`, `IC`, …).
-/

@[expose] public section

namespace Cslib.Byzantine.LockStep

variable {P I M O S V : Type*}

/-! ### Specifications depending only on honest decisions -/

/-- A specification that only depends on the decisions of honest parties. -/
def Spec.HonestOnly (spec : Spec P I O) : Prop :=
  ∀ x H d d', (∀ p ∈ H, ∀ o, d p o ↔ d' p o) → spec x H d → spec x H d'

lemma honestOnly_BB (b : P) : (BB b : Spec P V V).HonestOnly := by
  rintro x H d d' hd ⟨h1, h2, h3⟩
  exact ⟨fun p hp => (h1 p hp).imp fun v => (hd p hp v).mp,
    fun hb p hp => (hd p hp _).mp (h2 hb p hp),
    fun p hp q hq v w hv hw => h3 p hp q hq v w ((hd p hp v).mpr hv) ((hd q hq w).mpr hw)⟩

lemma honestOnly_BA : (BA : Spec P V V).HonestOnly := by
  rintro x H d d' hd ⟨h1, h2, h3⟩
  exact ⟨fun p hp => (h1 p hp).imp fun v => (hd p hp v).mp,
    fun v hv p hp => (hd p hp _).mp (h2 v hv p hp),
    fun p hp q hq v w hv hw => h3 p hp q hq v w ((hd p hp v).mpr hv) ((hd q hq w).mpr hw)⟩

lemma honestOnly_IC : (IC : Spec P V (P → V)).HonestOnly := by
  rintro x H d d' hd ⟨h1, h2, h3⟩
  exact ⟨fun p hp => (h1 p hp).imp fun v => (hd p hp v).mp,
    fun p hp e he => h2 p hp e ((hd p hp e).mpr he),
    fun p hp q hq v w hv hw => h3 p hp q hq v w ((hd p hp v).mpr hv) ((hd q hq w).mpr hw)⟩

lemma honestOnly_weakAgreement : (WeakAgreement : Spec P I (Option V)).HonestOnly := by
  intro x H d d' hd h p hp q hq v w hv hw
  exact h p hp q hq v w ((hd p hp _).mpr hv) ((hd q hq _).mpr hw)

lemma Spec.HonestOnly.someSpec {spec : Spec P I V} (hs : spec.HonestOnly) :
    (SomeSpec spec).HonestOnly := by
  rintro x H d d' hd ⟨h1, h2⟩
  exact ⟨fun p hp hn => h1 p hp ((hd p hp none).mpr hn),
    hs x H _ _ (fun p hp v => hd p hp (some v)) h2⟩

/-! ### First decisions in a run slowed down by a factor two -/

lemma firstSome_double {f g : ℕ → Option O} (h₀ : ∀ r, g (2 * r) = f r)
    (h₁ : ∀ r, g (2 * r + 1) = none) (o : O) : FirstSome g o ↔ FirstSome f o := by
  constructor
  · rintro ⟨k, hk, hlt⟩
    obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' k
    · refine ⟨r, (h₀ r) ▸ hk, fun r' hr' => ?_⟩
      rw [← h₀ r']; exact hlt _ (by omega)
    · simp [h₁] at hk
  · rintro ⟨r, hr, hlt⟩
    refine ⟨2 * r, (h₀ r).trans hr, fun k hk => ?_⟩
    obtain ⟨r', rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [h₀]; exact hlt _ (by omega)
    · exact h₁ r'

/-! ### Majority -/

open Classical in
/-- The value reported by a strict majority of `R` (if any). -/
noncomputable def majority (R : Finset P) (f : P → Option M) : Option M :=
  if h : ∃ m, R.card < 2 * (R.filter (fun w => f w = some m)).card then some h.choose else none

open Classical in
lemma exists_mem_inter_of_card_lt {R F₁ F₂ : Finset P} (h₁ : F₁ ⊆ R) (h₂ : F₂ ⊆ R)
    (h : R.card < F₁.card + F₂.card) : ∃ w ∈ F₁, w ∈ F₂ := by
  by_contra hc
  push Not at hc
  have hd : Disjoint F₁ F₂ := Finset.disjoint_left.mpr hc
  have := Finset.card_le_card (Finset.union_subset h₁ h₂)
  rw [Finset.card_union_of_disjoint hd] at this
  omega

open Classical in
/-- If the parties outside `B` are a strict majority of `R` and all report `m₀`, the majority
value is `m₀`. -/
lemma majority_eq {R : Finset P} {B : Set P} {f : P → Option M} {m₀ : Option M}
    (hB : 2 * (R.filter (· ∈ B)).card < R.card) (hf : ∀ w ∈ R, w ∉ B → f w = m₀) :
    majority R f = m₀ := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := R) (fun w => w ∈ B)
  set H := R.filter (fun w => w ∉ B) with hHdef
  have hH : R.card < 2 * H.card := by omega
  have hHR : H ⊆ R := Finset.filter_subset _ R
  have key : ∀ m, R.card < 2 * (R.filter (fun w => f w = some m)).card → m₀ = some m := by
    intro m hm
    obtain ⟨w, hw1, hw2⟩ := exists_mem_inter_of_card_lt (Finset.filter_subset _ R) hHR
      (show R.card < (R.filter (fun w => f w = some m)).card + H.card by omega)
    rw [Finset.mem_filter] at hw1
    rw [hHdef, Finset.mem_filter] at hw2
    rw [← hf w hw2.1 hw2.2, hw1.2]
  unfold majority
  split_ifs with h
  · exact (key _ h.choose_spec).symm
  · cases m₀ with
    | none => rfl
    | some m =>
      exfalso
      refine h ⟨m, lt_of_lt_of_le hH (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))⟩
      intro w hw
      rw [hHdef, Finset.mem_filter] at hw
      exact Finset.mem_filter.mpr ⟨hw.1, hf w hw.1 hw.2⟩

open Classical in
lemma majority_sound {R : Finset P} {f : P → Option M} {m : M} (h : majority R f = some m) :
    ∃ w ∈ R, f w = some m := by
  unfold majority at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  have hpos : 0 < (R.filter (fun w => f w = some hex.choose)).card := by
    have := hex.choose_spec; omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hw
  exact ⟨w, hw.1, hw.2⟩

/-! ### The compiled protocol -/

/-- A packet: wrapped messages `(origin, destination, simulated round, payload)` indexed by
destination (sent in even rounds) or by origin (forwarded in odd rounds). -/
abbrev Pkt (P M : Type*) := P → Option (P × P × ℕ × M)

/-- A relay rule: given the origin `u`, the destination `v`, the simulated round `r` and the
component `f w` that each `w` forwarded, the message `v` accepts from `u` (if any). -/
abbrev RelayRule (P M : Type*) := P → P → ℕ → Pkt P M → Option M

/-- A relay rule is sound if it only accepts payloads that some party forwarded. -/
def RelayRule.Sound (acc : RelayRule P M) : Prop :=
  ∀ u v r f m, acc u v r f = some m → ∃ w wr, f w = some wr ∧ wr.2.2.2 = m

variable (G G' : SimpleGraph P)

open Classical in
/-- Decoding the simulated round-`r` inbox of `v` from its two real inboxes. -/
noncomputable def decodeInbox (acc : RelayRule P M) (v : P) (r : ℕ)
    (ib₀ ib₁ : Inbox P (Pkt P M)) : Inbox P M := fun u =>
  if G.Adj u v then
    if G'.Adj u v then ((ib₀ u).bind (· v)).map (·.2.2.2)
    else acc u v r (fun w => (ib₁ w).bind (· u))
  else none

/-- Decoding a real history (pairs of inboxes, starting at simulated round `r`). -/
noncomputable def decodeAux (acc : RelayRule P M) (v : P) : ℕ → History P (Pkt P M) → History P M
  | r, ib₀ :: ib₁ :: h => decodeInbox G G' acc v r ib₀ ib₁ :: decodeAux acc v (r + 1) h
  | _, _ => []

/-- The simulated history decoded from a real history of `v`. -/
noncomputable def decodeHist (acc : RelayRule P M) (v : P) (h : History P (Pkt P M)) :
    History P M :=
  decodeAux G G' acc v 0 h

open Classical in
/-- The packet sent by `p` in simulated round `r` (history `h` of the simulated protocol). -/
noncomputable def packet (alg : Protocol P I M O) (p : P) (x : I) (h : History P M) (r : ℕ) :
    Pkt P M :=
  fun d => if G.Adj p d then (alg.send p x h d).map (fun m => (p, d, r, m)) else none

/-- The components destined to `q` of the packets received in the last round. -/
def forward (h : History P (Pkt P M)) (q : P) : Pkt P M :=
  fun u => ((h.getLastD fun _ => none) u).bind (· q)

/-- The compiled protocol on `G'` simulating `alg` on `G` with relay rule `acc`. -/
noncomputable def Protocol.relay (alg : Protocol P I M O) (acc : RelayRule P M) :
    Protocol P I (Pkt P M) O where
  send p x h q := some <|
    if h.length % 2 = 0 then packet G alg p x (decodeHist G G' acc p h) (h.length / 2)
    else forward h q
  decide p x h := if h.length % 2 = 0 then alg.decide p x (decodeHist G G' acc p h) else none

variable {G G'}

section decode

variable (acc : RelayRule P M) (v : P)

theorem decodeAux_append_pair :
    ∀ (n : ℕ) (h : History P (Pkt P M)) (r : ℕ) (a b : Inbox P (Pkt P M)), h.length = 2 * n →
      decodeAux G G' acc v r (h ++ [a, b]) =
        decodeAux G G' acc v r h ++ [decodeInbox G G' acc v (r + n) a b]
  | 0, [], r, a, b, _ => by simp [decodeAux]
  | 0, _ :: _, _, _, _, hl => by simp at hl
  | n + 1, [], _, _, _, hl => by simp at hl
  | n + 1, [_], _, _, _, hl => by simp at hl; omega
  | n + 1, ib₀ :: ib₁ :: h, r, a, b, hl => by
    have hl' : h.length = 2 * n := by simp at hl; omega
    simp only [List.cons_append, decodeAux]
    rw [decodeAux_append_pair n h (r + 1) a b hl']
    simp [Nat.add_assoc, Nat.add_comm 1 n]

theorem decodeAux_append_single :
    ∀ (n : ℕ) (h : History P (Pkt P M)) (r : ℕ) (a : Inbox P (Pkt P M)), h.length = 2 * n →
      decodeAux G G' acc v r (h ++ [a]) = decodeAux G G' acc v r h
  | 0, [], r, a, _ => by simp [decodeAux]
  | 0, _ :: _, _, _, hl => by simp at hl
  | n + 1, [], _, _, hl => by simp at hl
  | n + 1, [_], _, _, hl => by simp at hl; omega
  | n + 1, ib₀ :: ib₁ :: h, r, a, hl => by
    have hl' : h.length = 2 * n := by simp at hl; omega
    simp only [List.cons_append, decodeAux]
    rw [decodeAux_append_single n h (r + 1) a hl']

end decode

/-! ### Runs of the compiled protocol -/

section run

variable (alg : Protocol P I M O) (acc : RelayRule P M) (s' : Scenario P I (Pkt P M))

lemma relay_send_even {p : P} {x : I} {h : History P (Pkt P M)} {q : P} (hh : h.length % 2 = 0) :
    (alg.relay G G' acc).send p x h q =
      some (packet G alg p x (decodeHist G G' acc p h) (h.length / 2)) := by
  simp [Protocol.relay, hh]

lemma relay_send_odd {p : P} {x : I} {h : History P (Pkt P M)} {q : P} (hh : h.length % 2 = 1) :
    (alg.relay G G' acc).send p x h q = some (forward h q) := by
  simp [Protocol.relay, hh]

/-- The simulated round-`r` inbox of `v`, decoded from the real run. -/
noncomputable def simInbox (G G' : SimpleGraph P) (r : ℕ) (v : P) : Inbox P M :=
  decodeInbox G G' acc v r
    (fun u => deliver G' (alg.relay G G' acc) s' (hist G' (alg.relay G G' acc) s' (2 * r))
      (2 * r) u v)
    (fun w => deliver G' (alg.relay G G' acc) s' (hist G' (alg.relay G G' acc) s' (2 * r + 1))
      (2 * r + 1) w v)

lemma decodeHist_hist_two_mul_succ (r : ℕ) (v : P) :
    decodeHist G G' acc v (hist G' (alg.relay G G' acc) s' (2 * (r + 1)) v) =
      decodeHist G G' acc v (hist G' (alg.relay G G' acc) s' (2 * r) v) ++
        [simInbox alg acc s' G G' r v] := by
  rw [show 2 * (r + 1) = 2 * r + 1 + 1 by omega, hist_succ, hist_succ, List.append_assoc,
    List.singleton_append]
  rw [decodeHist, decodeAux_append_pair acc v r _ 0 _ _ (length_hist _ _ _ _ _)]
  simp [decodeHist, simInbox]

lemma decodeHist_hist_two_mul_add_one (r : ℕ) (v : P) :
    decodeHist G G' acc v (hist G' (alg.relay G G' acc) s' (2 * r + 1) v) =
      decodeHist G G' acc v (hist G' (alg.relay G G' acc) s' (2 * r) v) := by
  rw [hist_succ, decodeHist, decodeAux_append_single acc v r _ 0 _ (length_hist _ _ _ _ _)]
  rfl

/-- An honest packet sent in round `2r`. -/
lemma deliver_relay_even (r : ℕ) {u w : P} (hu : u ∉ s'.byz) (hd : ¬ s'.drop (2 * r) u w)
    (hadj : G'.Adj u w) :
    deliver G' (alg.relay G G' acc) s' (hist G' (alg.relay G G' acc) s' (2 * r)) (2 * r) u w =
      some (packet G alg u (s'.input u)
        (decodeHist G G' acc u (hist G' (alg.relay G G' acc) s' (2 * r) u)) r) := by
  rw [deliver, ite_eq_left hadj, ite_eq_right hu, ite_eq_right hd,
    relay_send_even alg acc (by rw [length_hist]; omega), length_hist]
  congr 3; omega

/-- An honest forwarding message sent in round `2r+1`. -/
lemma deliver_relay_odd (r : ℕ) {w v : P} (hw : w ∉ s'.byz) (hd : ¬ s'.drop (2 * r + 1) w v)
    (hadj : G'.Adj w v) :
    deliver G' (alg.relay G G' acc) s' (hist G' (alg.relay G G' acc) s' (2 * r + 1)) (2 * r + 1)
      w v = some (forward (hist G' (alg.relay G G' acc) s' (2 * r + 1) w) v) := by
  rw [deliver, ite_eq_left hadj, ite_eq_right hw, ite_eq_right hd,
    relay_send_odd alg acc (by rw [length_hist]; omega)]

lemma forward_hist (r : ℕ) (w v u : P) :
    forward (hist G' (alg.relay G G' acc) s' (2 * r + 1) w) v u =
      (deliver G' (alg.relay G G' acc) s' (hist G' (alg.relay G G' acc) s' (2 * r)) (2 * r)
        u w).bind (· v) := by
  rw [hist_succ]; simp [forward]

lemma status_relay_even (r : ℕ) (p : P) :
    status G' (alg.relay G G' acc) s' (2 * r) p =
      alg.decide p (s'.input p)
        (decodeHist G G' acc p (hist G' (alg.relay G G' acc) s' (2 * r) p)) := by
  simp [status, Protocol.relay, length_hist]

lemma status_relay_odd (r : ℕ) (p : P) :
    status G' (alg.relay G G' acc) s' (2 * r + 1) p = none := by
  have : (2 * r + 1) % 2 = 1 := by omega
  simp [status, Protocol.relay, length_hist, this]

/-- The scenario of `alg` on `G` simulated by the run of the compiled protocol: same Byzantine
parties and inputs, the Byzantine messages are what honest parties decode, omissions `D`. -/
noncomputable def simScenario (G G' : SimpleGraph P) (D : ℕ → P → P → Prop) : Scenario P I M where
  byz := s'.byz
  input := s'.input
  adv r b v := simInbox alg acc s' G G' r v b
  drop := D

open Classical in
/-- **History correspondence**: if decoding honest messages between honest parties is correct
whenever the histories correspond so far, then the decoded history of every honest party is its
history in the simulated scenario. -/
theorem hist_simScenario (D : ℕ → P → P → Prop)
    (hstep : ∀ r, (∀ p, p ∉ s'.byz → hist G alg (simScenario alg acc s' G G' D) r p =
        decodeHist G G' acc p (hist G' (alg.relay G G' acc) s' (2 * r) p)) →
      ∀ u v, u ∉ s'.byz → v ∉ s'.byz → G.Adj u v →
        simInbox alg acc s' G G' r v u = if D r u v then none
          else alg.send u (s'.input u) (hist G alg (simScenario alg acc s' G G' D) r u) v) :
    ∀ r p, p ∉ s'.byz → hist G alg (simScenario alg acc s' G G' D) r p =
      decodeHist G G' acc p (hist G' (alg.relay G G' acc) s' (2 * r) p) := by
  intro r
  induction r with
  | zero => intro p _; simp [decodeHist, decodeAux]
  | succ r ih =>
    intro v hv
    rw [hist_succ, ih v hv, decodeHist_hist_two_mul_succ]
    congr 2
    funext u
    rw [deliver]
    by_cases hadj : G.Adj u v
    · rw [ite_eq_left hadj]
      by_cases hu : u ∈ (simScenario alg acc s' G G' D).byz
      · rw [ite_eq_left hu]; rfl
      · rw [ite_eq_right hu, hstep r ih u v hu hv hadj]; rfl
    · rw [ite_eq_right hadj]; simp [simInbox, decodeInbox, hadj]

/-- Honest parties decide in the compiled run as in any run with corresponding histories. -/
theorem decides_relay_iff {s : Scenario P I M} {p : P} (hx : s.input p = s'.input p)
    (hh : ∀ r, hist G alg s r p = decodeHist G G' acc p (hist G' (alg.relay G G' acc) s' (2 * r) p))
    (o : O) : Decides G' (alg.relay G G' acc) s' p o ↔ Decides G alg s p o := by
  rw [decides_iff_firstSome, decides_iff_firstSome]
  refine firstSome_double (fun r => ?_) (fun r => status_relay_odd alg acc s' r p) o
  rw [status_relay_even, status, hh, hx]

/-- Termination within `T` simulated rounds gives termination within `2T` real rounds. -/
theorem terminatesBy_relay {s : Scenario P I M} (hB : s.byz = s'.byz)
    (hx : ∀ p, p ∉ s'.byz → s.input p = s'.input p)
    (hh : ∀ p, p ∉ s'.byz → ∀ r, hist G alg s r p =
      decodeHist G G' acc p (hist G' (alg.relay G G' acc) s' (2 * r) p))
    {T : ℕ} (hT : TerminatesBy G alg s T) : TerminatesBy G' (alg.relay G G' acc) s' (2 * T) := by
  intro p hp
  obtain ⟨r, hr, o, ho⟩ := hT p (hB ▸ hp)
  refine ⟨2 * r, by omega, o, ?_⟩
  rw [status_relay_even, ← hh p hp, ← hx p hp]
  exact ho

/-- Direct channels: an honest packet is decoded correctly. -/
lemma simInbox_direct (hrel : s'.Reliable) (r : ℕ) {u v : P} (hu : u ∉ s'.byz) (hadj : G.Adj u v)
    (hadj' : G'.Adj u v) :
    simInbox alg acc s' G G' r v u = alg.send u (s'.input u)
      (decodeHist G G' acc u (hist G' (alg.relay G G' acc) s' (2 * r) u)) v := by
  simp only [simInbox, decodeInbox, ite_eq_left hadj, ite_eq_left hadj']
  rw [deliver_relay_even alg acc s' r hu (hrel _ _ _) hadj']
  simp [packet, hadj, Option.map_map, Function.comp_def]

/-- What an honest relay `w` forwards from an honest origin `u` to `v`. -/
lemma forwarded_honest (hrel : s'.Reliable) (r : ℕ) {u w v : P} (hu : u ∉ s'.byz)
    (hw : w ∉ s'.byz) (huw : G'.Adj u w) (hwv : G'.Adj w v) :
    (deliver G' (alg.relay G G' acc) s' (hist G' (alg.relay G G' acc) s' (2 * r + 1)) (2 * r + 1)
      w v).bind (· u) = packet G alg u (s'.input u)
        (decodeHist G G' acc u (hist G' (alg.relay G G' acc) s' (2 * r) u)) r v := by
  rw [deliver_relay_odd alg acc s' r hw (hrel _ _ _) hwv, Option.bind_some, forward_hist,
    deliver_relay_even alg acc s' r hu (hrel _ _ _) huw, Option.bind_some]

end run

/-! ### Lemma 6: majority relay (unauthenticated) -/

/-- Majority relay rule. -/
noncomputable def majorityRule (Rel : P → P → Finset P) : RelayRule P M :=
  fun u v _ f => majority (Rel u v) (fun w => (f w).map (·.2.2.2))

lemma majorityRule_sound (Rel : P → P → Finset P) : (majorityRule Rel : RelayRule P M).Sound := by
  intro u v r f m h
  obtain ⟨w, -, hw⟩ := majority_sound h
  obtain ⟨wr, hwr, rfl⟩ := Option.map_eq_some_iff.mp hw
  exact ⟨w, wr, hwr, rfl⟩

section majority

variable {Rel : P → P → Finset P} (alg : Protocol P I M O)

open Classical in
/-- **Lemma 6** (simulation): with honest strict majorities in the relay sets of honest pairs,
every reliable run of the majority-relay compilation simulates a reliable run of `alg`. -/
theorem relay_majority_sim
    (hRel : ∀ u v w, G.Adj u v → ¬ G'.Adj u v → w ∈ Rel u v → G'.Adj u w ∧ G'.Adj w v)
    (s' : Scenario P I (Pkt P M)) (hrel : s'.Reliable)
    (hmaj : ∀ u v, u ∉ s'.byz → v ∉ s'.byz → G.Adj u v → ¬ G'.Adj u v →
      2 * ((Rel u v).filter (· ∈ s'.byz)).card < (Rel u v).card) :
    ∃ s : Scenario P I M, s.byz = s'.byz ∧ s.input = s'.input ∧ s.Reliable ∧
      (∀ p, p ∉ s'.byz → ∀ r, hist G alg s r p =
        decodeHist G G' (majorityRule Rel) p
          (hist G' (alg.relay G G' (majorityRule Rel)) s' (2 * r) p)) ∧
      (∀ p, p ∉ s'.byz → ∀ o, Decides G' (alg.relay G G' (majorityRule Rel)) s' p o ↔
        Decides G alg s p o) := by
  set acc : RelayRule P M := majorityRule Rel
  have hh := hist_simScenario (G := G) (G' := G') alg acc s' (fun _ _ _ => False) (by
    intro r ih u v hu hv hadj
    rw [ite_eq_right not_false, ih u hu]
    by_cases hadj' : G'.Adj u v
    · exact simInbox_direct (G := G) (G' := G') alg acc s' hrel r hu hadj hadj'
    · simp only [simInbox, decodeInbox, ite_eq_left hadj, ite_eq_right hadj', acc, majorityRule]
      refine majority_eq (hmaj u v hu hv hadj hadj') (fun w hw hwB => ?_)
      obtain ⟨huw, hwv⟩ := hRel u v w hadj hadj' hw
      rw [forwarded_honest (G := G) (G' := G') alg acc s' hrel r hu hwB huw hwv]
      simp [packet, hadj, Option.map_map, Function.comp_def]
      rfl)
  refine ⟨simScenario alg acc s' G G' (fun _ _ _ => False), rfl, rfl, fun _ _ _ h => h,
    fun p hp r => hh r p hp, fun p hp o => ?_⟩
  exact decides_relay_iff alg acc s' rfl (fun r => hh r p hp) o

open Classical in
/-- **Lemma 6**: the majority-relay compilation of a protocol solving `spec` on `G` solves `spec`
on `G'`, if honest parties are a strict majority of each relay set of an honest pair. -/
theorem Solves.relay_majority {Z : AdvStructure P} {spec : Spec P I O}
    (hRel : ∀ u v w, G.Adj u v → ¬ G'.Adj u v → w ∈ Rel u v → G'.Adj u w ∧ G'.Adj w v)
    (hmaj : ∀ B ∈ Z, ∀ u v, u ∉ B → v ∉ B → G.Adj u v → ¬ G'.Adj u v →
      2 * ((Rel u v).filter (· ∈ B)).card < (Rel u v).card)
    (hspec : spec.HonestOnly) (h : Solves G alg Z spec) :
    Solves G' (alg.relay G G' (majorityRule Rel)) Z spec := by
  intro s' hZ hrel
  obtain ⟨s, hB, hx, hs, -, hd⟩ := relay_majority_sim alg hRel s' hrel (hmaj _ hZ)
  have := h s (hB ▸ hZ) hs
  rw [Scenario.honest, hB, hx] at this
  exact hspec _ _ _ _ (fun p hp o => (hd p hp o).symm) this

open Classical in
/-- Termination is preserved by the majority-relay compilation (with twice as many rounds). -/
theorem terminatesBy_relay_majority
    (hRel : ∀ u v w, G.Adj u v → ¬ G'.Adj u v → w ∈ Rel u v → G'.Adj u w ∧ G'.Adj w v)
    (s' : Scenario P I (Pkt P M)) (hrel : s'.Reliable)
    (hmaj : ∀ u v, u ∉ s'.byz → v ∉ s'.byz → G.Adj u v → ¬ G'.Adj u v →
      2 * ((Rel u v).filter (· ∈ s'.byz)).card < (Rel u v).card) {T : ℕ}
    (hT : ∀ s : Scenario P I M, s.byz = s'.byz → s.Reliable → TerminatesBy G alg s T) :
    TerminatesBy G' (alg.relay G G' (majorityRule Rel)) s' (2 * T) := by
  obtain ⟨s, hB, hx, hs, hh, -⟩ := relay_majority_sim alg hRel s' hrel hmaj
  exact terminatesBy_relay alg _ s' hB (fun p _ => by rw [hx]) hh (hT s hB hs)

end majority

/-! ### Lemmas 8 and 10: signature relay (authenticated) -/

/-- The token structure of the compiled protocol: the tokens of the payloads, plus the wrappers
`(u, v, r, m)`, signed by `u`. -/
def Auth.relay (A : Auth P M S) : Auth P (Pkt P M) (S ⊕ (P × P × ℕ × M)) where
  signer := Sum.elim A.signer (fun wr => wr.1)
  tokens pk :=
    {τ | ∃ d wr, pk d = some wr ∧ (τ = Sum.inr wr ∨ ∃ t ∈ A.tokens wr.2.2.2, τ = Sum.inl t)}

open Classical in
/-- Signature relay rule: accept `m` if some relay forwarded the wrapper `(u, v, r, m)`. -/
noncomputable def sigRule (Rel : P → P → Finset P) : RelayRule P M := fun u v r f =>
  if h : ∃ m, ∃ w ∈ Rel u v, f w = some (u, v, r, m) then some h.choose else none

lemma sigRule_sound (Rel : P → P → Finset P) : (sigRule Rel : RelayRule P M).Sound := by
  intro u v r f m h
  unfold sigRule at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  obtain ⟨w, -, hw⟩ := hex.choose_spec
  exact ⟨w, _, hw, rfl⟩

lemma sigRule_eq_some {Rel : P → P → Finset P} {u v : P} {r : ℕ} {f : Pkt P M} {m : M}
    (h : sigRule Rel u v r f = some m) : ∃ w ∈ Rel u v, f w = some (u, v, r, m) := by
  unfold sigRule at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  exact hex.choose_spec

lemma sigRule_ne_none {Rel : P → P → Finset P} {u v : P} {r : ℕ} {f : Pkt P M} {m : M} {w : P}
    (hw : w ∈ Rel u v) (hf : f w = some (u, v, r, m)) : sigRule Rel u v r f ≠ none := by
  unfold sigRule
  rw [dite_eq_left ⟨m, w, hw, hf⟩]
  simp

section auth

variable (A : Auth P M S)

lemma Auth.mem_relay_tokens {pk : Pkt P M} {d : P} {wr : P × P × ℕ × M} (h : pk d = some wr) :
    Sum.inr wr ∈ A.relay.tokens pk ∧ ∀ t ∈ A.tokens wr.2.2.2, Sum.inl t ∈ A.relay.tokens pk :=
  ⟨⟨d, wr, h, Or.inl rfl⟩, fun t ht => ⟨d, wr, h, Or.inr ⟨t, ht, rfl⟩⟩⟩

lemma histTokens_decodeAux (acc : RelayRule P M) (hacc : acc.Sound) (v : P) :
    ∀ (r : ℕ) (h : History P (Pkt P M)),
      A.histTokens (decodeAux G G' acc v r h) ⊆ Sum.inl ⁻¹' A.relay.histTokens h
  | r, ib₀ :: ib₁ :: h => by
    rintro τ ⟨ib, hib, u, m, hm, hτm⟩
    simp only [decodeAux, List.mem_cons] at hib
    rcases hib with rfl | hib
    · simp only [decodeInbox] at hm
      split_ifs at hm with h1 h2
      · obtain ⟨wr, hwr, rfl⟩ := Option.map_eq_some_iff.mp hm
        obtain ⟨pk, hpk, hwr⟩ := Option.bind_eq_some_iff.mp hwr
        exact ⟨ib₀, by simp, u, pk, hpk, (A.mem_relay_tokens hwr).2 τ hτm⟩
      · obtain ⟨w, wr, hw, rfl⟩ := hacc _ _ _ _ _ hm
        obtain ⟨pk, hpk, hwr⟩ := Option.bind_eq_some_iff.mp hw
        exact ⟨ib₁, by simp, w, pk, hpk, (A.mem_relay_tokens hwr).2 τ hτm⟩
    · obtain ⟨ib', hib', rest⟩ := histTokens_decodeAux acc hacc v (r + 1) h ⟨ib, hib, u, m, hm, hτm⟩
      exact ⟨ib', by simp [hib'], rest⟩
  | r, [] => by intro τ hτ; simp [decodeAux, Auth.histTokens] at hτ
  | r, [_] => by intro τ hτ; simp [decodeAux, Auth.histTokens] at hτ

/-- **Unforgeability** of the compiled protocol. -/
theorem Protocol.Unforging.relay {alg : Protocol P I M O} (hU : alg.Unforging A)
    {acc : RelayRule P M} (hacc : acc.Sound) : (alg.relay G G' acc).Unforging A.relay := by
  intro p x h q m' hm τ hτ
  simp only [Protocol.relay, Option.some.injEq] at hm
  subst hm
  split_ifs at hτ with hh
  · obtain ⟨d, wr, hwr, hτ⟩ := hτ
    simp only [packet] at hwr
    split_ifs at hwr with hpd
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hwr
    rcases hτ with rfl | ⟨t, ht, rfl⟩
    · left; rfl
    · rcases hU _ _ _ _ _ hm t ht with hs | hs
      · left; exact hs
      · right; exact histTokens_decodeAux A acc hacc p 0 h hs
  · obtain ⟨u, wr, hwr, hτ⟩ := hτ
    simp only [forward] at hwr
    obtain ⟨pk, hpk, hwr⟩ := Option.bind_eq_some_iff.mp hwr
    right
    have hne : h ≠ [] := by rintro rfl; simp at hh
    refine ⟨h.getLastD fun _ => none, ?_, u, pk, hpk, ⟨q, wr, hwr, hτ⟩⟩
    rw [List.getLastD_eq_getLast? , List.getLast?_eq_some_getLast hne]
    exact List.getLast_mem hne

/-- In an authenticated run, a token in a message received by an honest party is signed by a
Byzantine party or was emitted by an honest party. -/
lemma token_delivered {Q N T : Type*} {H : SimpleGraph Q} {alg : Protocol Q I N O} {B : Auth Q N T}
    {s : Scenario Q I N} (hav : s.AuthValid H alg B) {k : ℕ} {u v : Q} {m : N} (hv : v ∉ s.byz)
    (hm : deliver H alg s (hist H alg s k) k u v = some m) {τ : T} (hτ : τ ∈ B.tokens m) :
    B.signer τ ∈ s.byz ∨ τ ∈ honestTokens H alg B s k := by
  unfold deliver at hm
  split_ifs at hm with hadj hu hd
  · exact hav k u v m hu hv hadj hm τ hτ
  · exact Or.inr ⟨k, le_rfl, u, hu, v, hadj, m, hm, hτ⟩

variable (alg : Protocol P I M O) (acc : RelayRule P M) (s' : Scenario P I (Pkt P M))

/-- A token occurring in the packet of an honest party in some simulated round `r' ≤ k / 2`. -/
def RelayOrigin (k : ℕ) (τ : S ⊕ (P × P × ℕ × M)) : Prop :=
  ∃ r', 2 * r' ≤ k ∧ ∃ p, p ∉ s'.byz ∧ τ ∈ A.relay.tokens (packet G alg p (s'.input p)
    (decodeHist G G' acc p (hist G' (alg.relay G G' acc) s' (2 * r') p)) r')

/-- **Provenance**: in an authenticated run of the compiled protocol, every honestly-signed token
emitted by an honest party originates in an honest packet. -/
theorem relayOrigin_of_honestTokens
    (hav : s'.AuthValid G' (alg.relay G G' acc) A.relay) :
    ∀ k τ, τ ∈ honestTokens G' (alg.relay G G' acc) A.relay s' k →
      A.relay.signer τ ∉ s'.byz → RelayOrigin A alg acc s' (G := G) (G' := G') k τ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rintro τ ⟨k', hk', p, hp, q, hpq, m, hm, hτ⟩ hs
  obtain ⟨r', rfl | rfl⟩ := Nat.even_or_odd' k'
  · rw [relay_send_even alg acc (by rw [length_hist]; omega), length_hist,
      show 2 * r' / 2 = r' by omega, Option.some.injEq] at hm
    subst hm
    exact ⟨r', hk', p, hp, hτ⟩
  · rw [relay_send_odd alg acc (by rw [length_hist]; omega), Option.some.injEq] at hm
    subst hm
    obtain ⟨d, wr, hwr, hτ'⟩ := hτ
    rw [forward_hist] at hwr
    obtain ⟨pk, hpk, hwr⟩ := Option.bind_eq_some_iff.mp hwr
    rcases token_delivered hav hp hpk ⟨q, wr, hwr, hτ'⟩ with hb | hb
    · exact absurd hb hs
    · obtain ⟨r'', hr'', rest⟩ := ih (2 * r') (by omega) τ hb hs
      exact ⟨r'', by omega, rest⟩

lemma relayOrigin_inl {k : ℕ} {t : S}
    (h : RelayOrigin A alg acc s' (G := G) (G' := G') k (Sum.inl t)) :
    ∃ r', 2 * r' ≤ k ∧ ∃ p, p ∉ s'.byz ∧ ∃ d, G.Adj p d ∧ ∃ m, alg.send p (s'.input p)
      (decodeHist G G' acc p (hist G' (alg.relay G G' acc) s' (2 * r') p)) d = some m ∧
        t ∈ A.tokens m := by
  obtain ⟨r', hr', p, hp, d, wr, hwr, hτ⟩ := h
  simp only [packet] at hwr
  split_ifs at hwr with hpd
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hwr
  rcases hτ with h | ⟨t', ht', h⟩
  · cases h
  · cases h
    exact ⟨r', hr', p, hp, d, hpd, m, hm, ht'⟩

lemma relayOrigin_inr {k : ℕ} {u v : P} {r : ℕ} {m : M}
    (h : RelayOrigin A alg acc s' (G := G) (G' := G') k (Sum.inr (u, v, r, m))) :
    alg.send u (s'.input u)
      (decodeHist G G' acc u (hist G' (alg.relay G G' acc) s' (2 * r) u)) v = some m := by
  obtain ⟨r', hr', p, hp, d, wr, hwr, hτ⟩ := h
  simp only [packet] at hwr
  split_ifs at hwr with hpd
  obtain ⟨m', hm', rfl⟩ := Option.map_eq_some_iff.mp hwr
  rcases hτ with h | ⟨t', ht', h⟩
  · cases h
    exact hm'
  · cases h

/-- A payload token in a decoded message comes from a message received in round `2r` or
`2r+1`. -/
lemma simInbox_tokens (hacc : acc.Sound) {r : ℕ} {u v : P} {m : M}
    (h : simInbox alg acc s' G G' r v u = some m) {t : S} (ht : t ∈ A.tokens m) :
    ∃ k ≤ 2 * r + 1, ∃ w pk, deliver G' (alg.relay G G' acc) s'
      (hist G' (alg.relay G G' acc) s' k) k w v = some pk ∧ Sum.inl t ∈ A.relay.tokens pk := by
  simp only [simInbox, decodeInbox] at h
  split_ifs at h with h1 h2
  · obtain ⟨wr, hwr, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨pk, hpk, hwr⟩ := Option.bind_eq_some_iff.mp hwr
    exact ⟨2 * r, by omega, u, pk, hpk, (A.mem_relay_tokens hwr).2 t ht⟩
  · obtain ⟨w, wr, hw, rfl⟩ := hacc _ _ _ _ _ h
    obtain ⟨pk, hpk, hwr⟩ := Option.bind_eq_some_iff.mp hw
    exact ⟨2 * r + 1, le_rfl, w, pk, hpk, (A.mem_relay_tokens hwr).2 t ht⟩

end auth

section sig

variable {Rel : P → P → Finset P} (A : Auth P M S) (alg : Protocol P I M O)

/-- **Lemmas 8 and 10** (simulation): every reliable authenticated run of the signature-relay
compilation simulates an authenticated run of `alg` on `G` with the same Byzantine parties and
inputs, in which honest messages are only lost between honest pairs all of whose relays are
Byzantine; honest parties decide identically in both runs. -/
theorem relay_sig_sim
    (hRel : ∀ u v w, G.Adj u v → ¬ G'.Adj u v → w ∈ Rel u v → G'.Adj u w ∧ G'.Adj w v)
    (s' : Scenario P I (Pkt P M)) (hrel : s'.Reliable)
    (hav : s'.AuthValid G' (alg.relay G G' (sigRule Rel)) A.relay) :
    ∃ s : Scenario P I M, s.byz = s'.byz ∧ s.input = s'.input ∧ s.AuthValid G alg A ∧
      (∀ r u v, s.drop r u v → u ∉ s.byz ∧ v ∉ s.byz ∧ G.Adj u v ∧ ¬ G'.Adj u v ∧
        ∀ w ∈ Rel u v, w ∈ s.byz) ∧
      (∀ p, p ∉ s'.byz → ∀ r, hist G alg s r p =
        decodeHist G G' (sigRule Rel) p
          (hist G' (alg.relay G G' (sigRule Rel)) s' (2 * r) p)) ∧
      (∀ p, p ∉ s'.byz → ∀ o, Decides G' (alg.relay G G' (sigRule Rel)) s' p o ↔
        Decides G alg s p o) := by
  set acc : RelayRule P M := sigRule Rel
  set D : ℕ → P → P → Prop := fun r u v => u ∉ s'.byz ∧ v ∉ s'.byz ∧ G.Adj u v ∧ ¬ G'.Adj u v ∧
    (∀ w ∈ Rel u v, w ∈ s'.byz) ∧ simInbox alg acc s' G G' r v u = none with hD
  have hh := hist_simScenario (G := G) (G' := G') alg acc s' D (by
    intro r ih u v hu hv hadj
    rw [ih u hu]
    set t := alg.send u (s'.input u)
      (decodeHist G G' acc u (hist G' (alg.relay G G' acc) s' (2 * r) u)) v with ht
    by_cases hadj' : G'.Adj u v
    · rw [ite_eq_right (fun h => h.2.2.2.1 hadj')]
      exact simInbox_direct (G := G) (G' := G') alg acc s' hrel r hu hadj hadj'
    -- (A) whatever is accepted is the true message
    have hA : ∀ m, simInbox alg acc s' G G' r v u = some m → t = some m := by
      intro m hm
      simp only [simInbox, decodeInbox, ite_eq_left hadj, ite_eq_right hadj'] at hm
      obtain ⟨w, -, hw⟩ := sigRule_eq_some hm
      obtain ⟨pk, hpk, hwr⟩ := Option.bind_eq_some_iff.mp hw
      rcases token_delivered hav hv hpk ((A.mem_relay_tokens hwr).1) with hb | hb
      · exact absurd hb hu
      · exact relayOrigin_inr A alg acc s'
          (relayOrigin_of_honestTokens A alg acc s' hav _ _ hb hu)
    -- (B) with an honest relay, the true message is accepted
    have hB : (∃ w ∈ Rel u v, w ∉ s'.byz) → simInbox alg acc s' G G' r v u = t := by
      rintro ⟨w, hw, hwB⟩
      cases htm : t with
      | none =>
        cases hs : simInbox alg acc s' G G' r v u with
        | none => rfl
        | some m => exact absurd (hA m hs) (by rw [htm]; simp)
      | some m =>
        obtain ⟨huw, hwv⟩ := hRel u v w hadj hadj' hw
        have hf := forwarded_honest (G := G) (G' := G') alg acc s' hrel r hu hwB huw hwv
        have hne : simInbox alg acc s' G G' r v u ≠ none := by
          simp only [simInbox, decodeInbox, ite_eq_left hadj, ite_eq_right hadj']
          refine sigRule_ne_none hw (m := m) ?_
          rw [hf]; simp [packet, hadj, ← ht, htm]
        obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.mp hne
        rw [hm', ← htm, hA m' hm']
    by_cases hDr : D r u v
    · rw [ite_eq_left hDr]; exact hDr.2.2.2.2.2
    · rw [ite_eq_right hDr]
      by_cases hall : ∀ w ∈ Rel u v, w ∈ s'.byz
      · have hne : simInbox alg acc s' G G' r v u ≠ none :=
          fun h => hDr ⟨hu, hv, hadj, hadj', hall, h⟩
        obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.mp hne
        rw [hm', hA m' hm']
      · push Not at hall
        exact hB hall)
  refine ⟨simScenario alg acc s' G G' D, rfl, rfl, ?_, ?_, fun p hp r => hh r p hp,
    fun p hp o => decides_relay_iff alg acc s' rfl (fun r => hh r p hp) o⟩
  · -- the simulated adversary is unforgeability-respecting
    intro r b v m hb hv hbv hm t ht
    obtain ⟨k, hk, w, pk, hpk, hpkt⟩ := simInbox_tokens A alg acc s' (sigRule_sound Rel) hm ht
    rcases token_delivered hav hv hpk hpkt with hs | hs
    · exact Or.inl hs
    · by_cases hts : A.signer t ∈ s'.byz
      · exact Or.inl hts
      obtain ⟨r', hr', p, hp, d, hpd, m', hm', htm'⟩ :=
        relayOrigin_inl A alg acc s' (relayOrigin_of_honestTokens A alg acc s' hav _ _ hs hts)
      refine Or.inr ⟨r', by omega, p, hp, d, hpd, m', ?_, htm'⟩
      rw [hh r' p hp]
      exact hm'
  · rintro r u v ⟨hu, hv, hadj, hadj', hall, -⟩
    exact ⟨hu, hv, hadj, hadj', hall⟩

/-- **Lemma 8**: if every pair of honest parties without a direct channel has an honest relay,
the signature-relay compilation of a protocol solving `spec` on `G` (authenticated) solves `spec`
on `G'` (authenticated). -/
theorem SolvesAuth.relay_sig {Z : AdvStructure P} {spec : Spec P I O}
    (hRel : ∀ u v w, G.Adj u v → ¬ G'.Adj u v → w ∈ Rel u v → G'.Adj u w ∧ G'.Adj w v)
    (hhon : ∀ B ∈ Z, ∀ u v, u ∉ B → v ∉ B → G.Adj u v → ¬ G'.Adj u v → ∃ w ∈ Rel u v, w ∉ B)
    (hspec : spec.HonestOnly) (h : SolvesAuth G alg A Z spec) :
    SolvesAuth G' (alg.relay G G' (sigRule Rel)) A.relay Z spec := by
  intro s' hZ hrel hav
  obtain ⟨s, hB, hx, hsav, hdrop, -, hd⟩ := relay_sig_sim A alg hRel s' hrel hav
  have hs : s.Reliable := by
    intro r u v hr
    obtain ⟨hu, hv, hadj, hadj', hall⟩ := hdrop r u v hr
    rw [hB] at hu hv hall
    obtain ⟨w, hw, hwB⟩ := hhon _ hZ u v hu hv hadj hadj'
    exact hwB (hall w hw)
  have := h s (hB ▸ hZ) hs hsav
  rw [Scenario.honest, hB, hx] at this
  exact hspec _ _ _ _ (fun p hp o => (hd p hp o).symm) this

/-- **Lemma 10**: a protocol whose guarantees `specOm` survive omissions between honest pairs all of
whose relays are Byzantine keeps them under the signature-relay compilation (on reliable `G'`). -/
theorem relay_sig_omissions {Z : AdvStructure P} {specOm : Spec P I O}
    (hRel : ∀ u v w, G.Adj u v → ¬ G'.Adj u v → w ∈ Rel u v → G'.Adj u w ∧ G'.Adj w v)
    (hspec : specOm.HonestOnly)
    (h : ∀ s : Scenario P I M, s.byz ∈ Z → s.AuthValid G alg A →
      (∀ r u v, s.drop r u v → u ∉ s.byz ∧ v ∉ s.byz ∧ G.Adj u v ∧ ¬ G'.Adj u v ∧
        ∀ w ∈ Rel u v, w ∈ s.byz) → specOm s.input s.honest (Decides G alg s))
    (s' : Scenario P I (Pkt P M)) (hZ : s'.byz ∈ Z) (hrel : s'.Reliable)
    (hav : s'.AuthValid G' (alg.relay G G' (sigRule Rel)) A.relay) :
    specOm s'.input s'.honest (Decides G' (alg.relay G G' (sigRule Rel)) s') := by
  obtain ⟨s, hB, hx, hsav, hdrop, -, hd⟩ := relay_sig_sim A alg hRel s' hrel hav
  have := h s (hB ▸ hZ) hsav hdrop
  rw [Scenario.honest, hB, hx] at this
  exact hspec _ _ _ _ (fun p hp o => (hd p hp o).symm) this

/-- Termination under the signature-relay compilation (with twice as many rounds). -/
theorem terminatesBy_relay_sig
    (hRel : ∀ u v w, G.Adj u v → ¬ G'.Adj u v → w ∈ Rel u v → G'.Adj u w ∧ G'.Adj w v)
    (s' : Scenario P I (Pkt P M)) (hrel : s'.Reliable)
    (hav : s'.AuthValid G' (alg.relay G G' (sigRule Rel)) A.relay) {T : ℕ}
    (hT : ∀ s : Scenario P I M, s.byz = s'.byz → s.AuthValid G alg A →
      (∀ r u v, s.drop r u v → u ∉ s.byz ∧ v ∉ s.byz ∧ G.Adj u v ∧ ¬ G'.Adj u v ∧
        ∀ w ∈ Rel u v, w ∈ s.byz) → TerminatesBy G alg s T) :
    TerminatesBy G' (alg.relay G G' (sigRule Rel)) s' (2 * T) := by
  obtain ⟨s, hB, hx, hsav, hdrop, hh, -⟩ := relay_sig_sim A alg hRel s' hrel hav
  exact terminatesBy_relay alg _ s' hB (fun p _ => by rw [hx]) hh (hT s hB hsav hdrop)

end sig

/-! ### Solvability -/

section solvable

open Classical in
/-- **Lemma 6** (solvability form). -/
theorem Solvable.relay_majority {P : Type} {G G' : SimpleGraph P} {Rel : P → P → Finset P}
    {Z : AdvStructure P} {spec : Spec P I O}
    (hRel : ∀ u v w, G.Adj u v → ¬ G'.Adj u v → w ∈ Rel u v → G'.Adj u w ∧ G'.Adj w v)
    (hmaj : ∀ B ∈ Z, ∀ u v, u ∉ B → v ∉ B → G.Adj u v → ¬ G'.Adj u v →
      2 * ((Rel u v).filter (· ∈ B)).card < (Rel u v).card)
    (hspec : spec.HonestOnly) (h : Solvable G Z spec) : Solvable G' Z spec := by
  obtain ⟨M, alg, h⟩ := h
  exact ⟨Pkt P M, alg.relay G G' (majorityRule Rel), h.relay_majority alg hRel hmaj hspec⟩

/-- **Lemma 8** (solvability form). -/
theorem SolvableAuth.relay_sig {P : Type} {G G' : SimpleGraph P} {Rel : P → P → Finset P}
    {Z : AdvStructure P} {spec : Spec P I O}
    (hRel : ∀ u v w, G.Adj u v → ¬ G'.Adj u v → w ∈ Rel u v → G'.Adj u w ∧ G'.Adj w v)
    (hhon : ∀ B ∈ Z, ∀ u v, u ∉ B → v ∉ B → G.Adj u v → ¬ G'.Adj u v → ∃ w ∈ Rel u v, w ∉ B)
    (hspec : spec.HonestOnly) (h : SolvableAuth G Z spec) : SolvableAuth G' Z spec := by
  obtain ⟨M, S, A, alg, hU, h⟩ := h
  exact ⟨Pkt P M, S ⊕ (P × P × ℕ × M), A.relay, alg.relay G G' (sigRule Rel),
    hU.relay A (sigRule_sound Rel), h.relay_sig A alg hRel hhon hspec⟩

end solvable

end Cslib.Byzantine.LockStep
