/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.CanonicalRounds.Lemmas
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Well-formedness, FIFO delivery and liveness of canonical-round executions

General facts about executions of an arbitrary canonical-round algorithm under an arbitrary
adversary (`Cslib.Byzantine.CanonicalRounds.CanonAlg.exec`):

* `ccView` basics: it keeps all draws (`rnd_ccView`), is a sublist of the history
  (`ccView_sublist`), and keeps all round-`r` messages of a history of round `≤ r`
  (`senders_ccView_of_rnd_le`).
* The cascade only appends draws (`exists_adv_eq`).
* `WellFormed`: in every history, each draw except the first is preceded by a quorum for the
  current round (`wellFormed_exec`). Hence a process whose history contains round-`r` messages
  from `n - f` senders has a *communication-closed* quorum for round `r` at a history prefix of
  round `≤ r` (`exists_ccQuorum`).
* FIFO: the messages a correct process has received from `q` are exactly the first `dlvd p q`
  messages sent by `q` to it (`fifoInv_exec`); in particular every message a correct process
  received was sent (`mem_sent_of_recv`), and a message received from a correct process carries
  the content `msg` computed from a prefix of the sender's history (`exists_msg_of_recv`).
* Fair executions: every message sent to a correct process is eventually received
  (`exists_recv_of_fair`); every correct process eventually holds a round-1 message of every
  correct process (`exists_senders_one_of_fair`).
* The oblivious round-robin adversary `rrAdv F` is admissible for every algorithm whenever
  `F.card ≤ f` (`rrAdv_admissible`), so statements quantified over admissible adversaries are not
  vacuous.
* `AllDecideBy r` bounds `rounds` by `r` and implies `AllDecide` (`rounds_le_of_allDecideBy`,
  `allDecide_of_allDecideBy`).
-/

@[expose] public section

namespace Cslib.Byzantine.CanonicalRounds

variable {n : ℕ} {V R M O : Type*}

/-! ### The communication-closed view -/

@[simp] theorem ccView_nil : ccView ([] : Log n R M) = [] := rfl

theorem ccView_append_singleton (l : Log n R M) (e : Entry n R M) :
    ccView (l ++ [e]) = ccStep (ccView l) e := by
  simp [ccView, List.foldl_append]

/-- The communication-closed view keeps every draw, hence the round. -/
@[simp] theorem rnd_ccView (l : Log n R M) : rnd (ccView l) = rnd l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    rw [ccView_append_singleton]
    cases e with
    | draw x => simp [ccStep, ih]
    | recv q r m => simp only [ccStep]; split_ifs <;> simp [ih]

theorem ccView_sublist (l : Log n R M) : List.Sublist (ccView l) l := by
  induction l using List.reverseRecOn with
  | nil => exact List.Sublist.slnil
  | append_singleton l e ih =>
    rw [ccView_append_singleton]
    cases e with
    | draw x => exact ih.append (List.Sublist.refl _)
    | recv q r m =>
      simp only [ccStep]
      split_ifs
      · exact ih.append (List.Sublist.refl _)
      · exact ih.trans (List.sublist_append_left _ _)

/-- In a history of round `≤ r` no round-`r` message is late: the communication-closed view has
the same round-`r` senders. -/
theorem senders_ccView_of_rnd_le {r : ℕ} {l : Log n R M} (h : rnd l ≤ r) :
    senders r (ccView l) = senders r l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e ih =>
    rw [ccView_append_singleton]
    have hl : rnd l ≤ r := le_trans (rnd_mono (List.prefix_append _ _)) h
    cases e with
    | draw x => simp only [ccStep, senders_append_draw, ih hl]
    | recv q r' m =>
      simp only [ccStep]
      by_cases hr : r' = r
      · subst hr
        have : rnd (ccView l) ≤ r' := by rw [rnd_ccView]; exact hl
        simp only [this, ↓reduceIte, senders_append_recv, ih hl]
      · split_ifs <;> simp [senders_append_recv_of_ne _ _ _ _ _ hr, ih hl]

/-! ### The cascade only appends draws -/

theorem exists_advance_eq (f : ℕ) (ρp : ℕ → R) :
    ∀ (k : ℕ) (l : Log n R M), ∃ xs : List R, advance f ρp k l = l ++ xs.map Entry.draw
  | 0, l => ⟨[], by simp [advance]⟩
  | k + 1, l => by
    unfold advance
    split_ifs
    · obtain ⟨xs, hxs⟩ := exists_advance_eq f ρp k (l ++ [Entry.draw (ρp (rnd l + 1))])
      exact ⟨ρp (rnd l + 1) :: xs, by rw [hxs]; simp⟩
    · exact ⟨[], by simp⟩

theorem exists_adv_eq (f : ℕ) (ρp : ℕ → R) (l : Log n R M) :
    ∃ xs : List R, adv f ρp l = l ++ xs.map Entry.draw :=
  exists_advance_eq f ρp _ l

/-! ### Draws and quorums -/

/-- If the round of `l` exceeds `j`, then `l` has a prefix ending with the draw that starts round
`j + 1`. -/
theorem exists_draw_prefix {l : Log n R M} {j : ℕ} (h : j < rnd l) :
    ∃ h' x, h' ++ [Entry.draw x] <+: l ∧ rnd h' = j := by
  induction l using List.reverseRecOn with
  | nil => simp at h
  | append_singleton l e ih =>
    cases e with
    | recv q r m =>
      simp only [rnd_append, rnd_recv, add_zero] at h
      obtain ⟨h', x, hp, hr⟩ := ih h
      exact ⟨h', x, hp.trans (List.prefix_append _ _), hr⟩
    | draw x =>
      simp only [rnd_append, rnd_draw] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
      · obtain ⟨h', x', hp, hr⟩ := ih h
        exact ⟨h', x', hp.trans (List.prefix_append _ _), hr⟩
      · exact ⟨l, x, List.prefix_refl _, rfl⟩

/-- Well-formedness of a history: every draw except the first one is taken when the process has
a quorum for its current round. -/
def WellFormed (f : ℕ) (l : Log n R M) : Prop :=
  ∀ h x, h ++ [Entry.draw x] <+: l → rnd h = 0 ∨ Quorum f h

theorem wellFormed_nil (f : ℕ) : WellFormed f ([] : Log n R M) := by
  intro h x hh; simpa using hh.length_le

theorem wellFormed_snoc {f : ℕ} {l : Log n R M} (hl : WellFormed f l) (e : Entry n R M)
    (he : ∀ x, e = .draw x → rnd l = 0 ∨ Quorum f l) : WellFormed f (l ++ [e]) := by
  intro h x hh
  rcases List.prefix_concat_iff.1 hh with h1 | h1
  · obtain ⟨rfl, h2⟩ := List.append_inj' h1 rfl
    simp only [List.cons.injEq, and_true] at h2
    exact he x h2.symm
  · exact hl h x h1

theorem wellFormed_advance {f : ℕ} {ρp : ℕ → R} :
    ∀ (k : ℕ) {l : Log n R M}, WellFormed f l → WellFormed f (advance f ρp k l)
  | 0, l, hl => hl
  | k + 1, l, hl => by
    unfold advance
    split_ifs with hq
    · exact wellFormed_advance k (wellFormed_snoc hl _ fun _ _ => Or.inr hq)
    · exact hl

theorem wellFormed_adv {f : ℕ} {ρp : ℕ → R} {l : Log n R M} (hl : WellFormed f l)
    (e : Entry n R M) (he : ∀ x, e = .draw x → rnd l = 0 ∨ Quorum f l) :
    WellFormed f (adv f ρp (l ++ [e])) :=
  wellFormed_advance _ (wellFormed_snoc hl e he)

/-- A well-formed history containing round-`r` messages from `n - f` senders (`r ≥ 1`) has a
prefix of round `≤ r` whose communication-closed view contains round-`r` messages from `n - f`
senders: either the history itself is still in round `≤ r`, or the draw starting round `r + 1`
was preceded by a quorum for round `r`. -/
theorem exists_ccQuorum {f r : ℕ} {l : Log n R M} (hwf : WellFormed f l) (hr : 1 ≤ r)
    (hl : n - f ≤ (senders r l).card) :
    ∃ h, h <+: l ∧ rnd h ≤ r ∧ n - f ≤ (senders r (ccView h)).card := by
  by_cases hlr : rnd l ≤ r
  · exact ⟨l, List.prefix_refl _, hlr, by rwa [senders_ccView_of_rnd_le hlr]⟩
  · obtain ⟨h, x, hp, hrh⟩ := exists_draw_prefix (lt_of_not_ge hlr)
    rcases hwf h x hp with h0 | ⟨-, hq⟩
    · omega
    · refine ⟨h, (List.prefix_append _ _).trans hp, hrh.le, ?_⟩
      rw [senders_ccView_of_rnd_le hrh.le]
      rwa [hrh] at hq

/-! ### Messages received from a given sender -/

/-- The message carried by an entry, if it is a message received from `q`. -/
def Entry.recvOf? (q : Fin n) : Entry n R M → Option (ℕ × M)
  | .recv q' r m => if q' = q then some (r, m) else none
  | .draw _ => none

/-- The messages (round label, content) received from `q`, in order of reception. -/
def recvFrom (q : Fin n) (l : Log n R M) : List (ℕ × M) := l.filterMap (Entry.recvOf? q)

theorem recvFrom_append (q : Fin n) (l l' : Log n R M) :
    recvFrom q (l ++ l') = recvFrom q l ++ recvFrom q l' := List.filterMap_append

@[simp] theorem recvFrom_map_draw (q : Fin n) (xs : List R) :
    recvFrom q (xs.map Entry.draw : Log n R M) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [recvFrom, Entry.recvOf?]

theorem recvFrom_recv_self (q : Fin n) (r : ℕ) (m : M) :
    recvFrom q ([.recv q r m] : Log n R M) = [(r, m)] := by
  simp [recvFrom, Entry.recvOf?]

theorem recvFrom_recv_of_ne {q q' : Fin n} (h : q' ≠ q) (r : ℕ) (m : M) :
    recvFrom q ([.recv q' r m] : Log n R M) = [] := by
  simp [recvFrom, Entry.recvOf?, h]

theorem mem_recvFrom {q : Fin n} {r : ℕ} {m : M} {l : Log n R M} :
    (r, m) ∈ recvFrom q l ↔ Entry.recv q r m ∈ l := by
  simp only [recvFrom, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, h⟩
    cases e with
    | draw x => simp [Entry.recvOf?] at h
    | recv q' r' m' =>
      simp only [Entry.recvOf?, Option.ite_none_right_eq_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact he
  · intro h; exact ⟨_, h, by simp [Entry.recvOf?]⟩

theorem take_eq_of_prefix {α : Type*} {s s' : List α} (h : s <+: s') {d : ℕ}
    (hd : d ≤ s.length) : s'.take d = s.take d := by
  rw [List.prefix_iff_eq_take.1 h, List.take_take, min_eq_left hd]

theorem getElem?_eq_of_prefix {α : Type*} {s s' : List α} (h : s <+: s') {i : ℕ} {a : α}
    (hi : s[i]? = some a) : s'[i]? = some a := by
  rw [List.prefix_iff_eq_take.1 h, List.getElem?_take] at hi
  split_ifs at hi
  exact hi

/-! ### FIFO delivery -/

namespace CanonAlg

variable (alg : CanonAlg n V R M O) (f : ℕ) (I : Fin n → V) (ρ : Tape n R)

/-- FIFO invariant for the link from `q` to `p`: `p` has received exactly the first `dlvd p q`
messages sent by `q` to `p`. -/
def FifoInv (F : Finset (Fin n)) (c : Config n R M) (p q : Fin n) : Prop :=
  recvFrom q (c.log p) = (alg.sent I F c q p).take (c.dlvd p q) ∧
    c.dlvd p q ≤ (alg.sent I F c q p).length

theorem FifoInv.of_le {F : Finset (Fin n)} {c c' : Config n R M} {p q : Fin n}
    (h : alg.FifoInv I F c p q) (hle : Le c c')
    (hlog : recvFrom q (c'.log p) = recvFrom q (c.log p))
    (hd : c'.dlvd p q = c.dlvd p q) : alg.FifoInv I F c' p q := by
  have hs := alg.sent_prefix I F hle q p
  refine ⟨?_, ?_⟩
  · rw [hlog, hd, h.1, take_eq_of_prefix hs h.2]
  · rw [hd]; exact h.2.trans hs.length_le

theorem fifoInv_step {F : Finset (Fin n)} {c : Config n R M} {p q : Fin n}
    (h : alg.FifoInv I F c p q) (e : Event n M) : alg.FifoInv I F (alg.step f I F ρ c e) p q := by
  have hle := alg.le_step f I F ρ c e
  cases e with
  | wake p' =>
    refine h.of_le alg I hle ?_ ?_
    · simp only [step]; split_ifs
      · rcases eq_or_ne p p' with rfl | hne
        · simp only [Function.update_self]
          obtain ⟨xs, hxs⟩ := exists_adv_eq f (ρ p) (c.log p ++ [Entry.draw (ρ p 1)])
          rw [hxs, recvFrom_append, recvFrom_append, recvFrom_map_draw]
          simp [recvFrom, Entry.recvOf?]
        · simp [hne]
      · rfl
    · simp only [step]; split_ifs <;> rfl
  | deliver p' q' =>
    revert hle
    simp only [step]
    split_ifs with hp'
    · exact fun hle => h.of_le alg I hle rfl rfl
    · split
      · next w hw =>
        intro hle
        have hs := alg.sent_prefix I F hle q p
        rcases eq_or_ne p p' with rfl | hne
        · obtain ⟨xs, hxs⟩ := exists_adv_eq f (ρ p) (c.log p ++ [Entry.recv q' w.1 w.2])
          rcases eq_or_ne q q' with rfl | hq
          · have hlt : c.dlvd p q < (alg.sent I F c q p).length := by
              by_contra hc; rw [List.getElem?_eq_none (by omega)] at hw; simp at hw
            refine ⟨?_, ?_⟩
            · simp only [Function.update_self] at hs ⊢
              rw [take_eq_of_prefix hs (by omega), List.take_add_one, hw, hxs, recvFrom_append,
                recvFrom_append, recvFrom_recv_self, recvFrom_map_draw, h.1]
              simp
            · simp only [Function.update_self] at hs ⊢
              exact le_trans (by omega) hs.length_le
          · refine h.of_le alg I hle ?_ ?_
            · simp only [Function.update_self]
              rw [hxs, recvFrom_append, recvFrom_append, recvFrom_recv_of_ne hq.symm,
                recvFrom_map_draw]
              simp
            · simp [hq]
        · exact h.of_le alg I hle (by simp [hne]) (by simp [hne])
      · exact fun hle => h.of_le alg I hle rfl rfl
  | byz q' p' r m =>
    refine h.of_le alg I hle ?_ ?_ <;> simp only [step] <;> split_ifs <;> rfl
  | skip => exact h.of_le alg I hle rfl rfl

/-- FIFO: in every execution, every correct process has received exactly the first `dlvd p q`
messages sent to it by `q`. -/
theorem fifoInv_exec (A : Adversary n R M) (k : ℕ) (p q : Fin n) :
    alg.FifoInv I A.F (alg.exec f I ρ A k) p q := by
  induction k with
  | zero => simp [FifoInv, exec, Config.init, recvFrom]
  | succ k ih => exact alg.fifoInv_step f I ρ ih _

/-- Every message in the history of a correct process was sent to it. -/
theorem mem_sent_of_recv (A : Adversary n R M) (k : ℕ) {p q : Fin n} {r : ℕ} {m : M}
    (h : Entry.recv q r m ∈ (alg.exec f I ρ A k).log p) :
    (r, m) ∈ alg.sent I A.F (alg.exec f I ρ A k) q p := by
  rw [← mem_recvFrom, (alg.fifoInv_exec f I ρ A k p q).1] at h
  exact List.mem_of_mem_take h

/-- A message in a correct process' outbox is computed by `msg` from a prefix of its history. -/
theorem exists_msg_of_mem_outbox {q : Fin n} {v : V} {l : Log n R M} {r : ℕ} {m : M}
    (h : (r, m) ∈ alg.outbox q v l) :
    ∃ h' x, h' ++ [Entry.draw x] <+: l ∧ r = rnd h' + 1 ∧ m = alg.msg q v (h' ++ [.draw x]) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
  obtain ⟨h', x, hp, hr, hw⟩ := alg.outbox_getElem q v l i _ hi
  simp only [Prod.mk.injEq] at hw
  exact ⟨h', x, hp, by omega, hw.2⟩

/-- A message received from a correct sender `q` was computed by `msg` from a prefix of `q`'s
history (with `q`'s input). -/
theorem exists_msg_of_recv (A : Adversary n R M) (k : ℕ) {p q : Fin n}
    (hq : q ∉ A.F) {r : ℕ} {m : M} (h : Entry.recv q r m ∈ (alg.exec f I ρ A k).log p) :
    ∃ h' x, h' ++ [Entry.draw x] <+: (alg.exec f I ρ A k).log q ∧ r = rnd h' + 1 ∧
      m = alg.msg q (I q) (h' ++ [.draw x]) := by
  have := alg.mem_sent_of_recv f I ρ A k h
  simp only [sent, hq, ite_false] at this
  exact alg.exists_msg_of_mem_outbox this

/-! ### Well-formedness of executions -/

/-- Every history in every execution is well formed: a process only starts a round `≥ 2` after
a quorum for its current round. -/
theorem wellFormed_exec (A : Adversary n R M) (k : ℕ) (p : Fin n) :
    WellFormed f ((alg.exec f I ρ A k).log p) := by
  induction k with
  | zero => exact wellFormed_nil f
  | succ k ih =>
    simp only [exec]
    generalize A.ev k (alg.exec f I ρ A k) = e
    generalize alg.exec f I ρ A k = c at ih
    cases e with
    | wake p' =>
      simp only [step]; split_ifs with hw
      · rcases eq_or_ne p p' with rfl | hne
        · simp only [Function.update_self]
          exact wellFormed_adv ih _ (fun _ _ => Or.inl hw.2)
        · simpa [hne] using ih
      · exact ih
    | deliver p' q =>
      simp only [step]; split_ifs
      · exact ih
      · split
        · rcases eq_or_ne p p' with rfl | hne
          · simp only [Function.update_self]
            exact wellFormed_adv ih _ (fun x hx => by cases hx)
          · simpa [hne] using ih
        · exact ih
    | byz q p' r m => simp only [step]; split_ifs <;> exact ih
    | skip => exact ih

/-! ### Fair executions: eventual delivery -/

theorem dlvd_step_deliver {F : Finset (Fin n)} {c : Config n R M} {p q : Fin n} (hp : p ∉ F)
    (h : c.dlvd p q < (alg.sent I F c q p).length) :
    (alg.step f I F ρ c (.deliver p q)).dlvd p q = c.dlvd p q + 1 := by
  obtain ⟨w, hw⟩ : ∃ w, (alg.sent I F c q p)[c.dlvd p q]? = some w :=
    ⟨_, List.getElem?_eq_getElem h⟩
  simp only [step, hp, ite_false]
  split
  · simp
  · next h' => rw [hw] at h'; cases h'

/-- In a fair execution, every message sent to a correct process `p` is eventually delivered:
the delivery counter of the link eventually exceeds its index. -/
theorem exists_dlvd_gt (A : Adversary n R M) (hfair : alg.Fair f I ρ A) {p : Fin n}
    (hp : p ∉ A.F) (q : Fin n) {i k₀ : ℕ}
    (hi : i < (alg.sent I A.F (alg.exec f I ρ A k₀) q p).length) :
    ∃ k ≥ k₀, i < (alg.exec f I ρ A k).dlvd p q := by
  suffices H : ∀ d k₀, i + 1 - (alg.exec f I ρ A k₀).dlvd p q ≤ d →
      i < (alg.sent I A.F (alg.exec f I ρ A k₀) q p).length →
      ∃ k ≥ k₀, i < (alg.exec f I ρ A k).dlvd p q from H _ k₀ le_rfl hi
  intro d
  induction d with
  | zero => intro k₀ hd _; exact ⟨k₀, le_rfl, by omega⟩
  | succ d ih =>
    intro k₀ hd hi
    by_cases h0 : i < (alg.exec f I ρ A k₀).dlvd p q
    · exact ⟨k₀, le_rfl, h0⟩
    obtain ⟨k', hk', hev⟩ := hfair.2 p hp q k₀
    have hle := alg.le_exec f I ρ A hk'
    by_cases h1 : i < (alg.exec f I ρ A k').dlvd p q
    · exact ⟨k', hk', h1⟩
    have hlen : (alg.exec f I ρ A k').dlvd p q <
        (alg.sent I A.F (alg.exec f I ρ A k') q p).length :=
      lt_of_le_of_lt (not_lt.1 h1) (lt_of_lt_of_le hi (alg.sent_prefix I A.F hle q p).length_le)
    have hstep : (alg.exec f I ρ A (k' + 1)).dlvd p q = (alg.exec f I ρ A k').dlvd p q + 1 := by
      change (alg.step f I A.F ρ _ (A.ev k' _)).dlvd p q = _
      rw [hev]; exact alg.dlvd_step_deliver f I ρ hp hlen
    have hd0 := hle.dlvd p q
    obtain ⟨k, hk, hik⟩ := ih (k' + 1) (by omega)
      (lt_of_lt_of_le hi (alg.sent_prefix I A.F
        (alg.le_exec f I ρ A (by omega : k₀ ≤ k' + 1)) q p).length_le)
    exact ⟨k, by omega, hik⟩

/-- In a fair execution, every message sent to a correct process is eventually received. -/
theorem exists_recv_of_fair (A : Adversary n R M) (hfair : alg.Fair f I ρ A) {p : Fin n}
    (hp : p ∉ A.F) (q : Fin n) {k₀ i : ℕ} {w : ℕ × M}
    (hw : (alg.sent I A.F (alg.exec f I ρ A k₀) q p)[i]? = some w) :
    ∃ k ≥ k₀, Entry.recv q w.1 w.2 ∈ (alg.exec f I ρ A k).log p := by
  have hi : i < (alg.sent I A.F (alg.exec f I ρ A k₀) q p).length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hw; cases hw
  obtain ⟨k, hk, hik⟩ := alg.exists_dlvd_gt f I ρ A hfair hp q hi
  refine ⟨k, hk, ?_⟩
  rw [← mem_recvFrom, (alg.fifoInv_exec f I ρ A k p q).1]
  have hw' := getElem?_eq_of_prefix (alg.sent_prefix I A.F (alg.le_exec f I ρ A hk) q p) hw
  refine List.mem_iff_getElem?.2 ⟨i, ?_⟩
  simp only [List.getElem?_take, hik, ↓reduceIte, hw']

/-- In a fair execution, every correct process eventually receives the round-1 message of every
correct process. -/
theorem exists_recv_one_of_fair (A : Adversary n R M) (hfair : alg.Fair f I ρ A) {p q : Fin n}
    (hp : p ∉ A.F) (hq : q ∉ A.F) : ∃ k, q ∈ senders 1 ((alg.exec f I ρ A k).log p) := by
  obtain ⟨k₀, hk₀⟩ := hfair.1 q hq
  have hlen : 0 < (alg.sent I A.F (alg.exec f I ρ A k₀) q p).length := by
    simp only [sent, hq, ite_false, length_outbox]; omega
  obtain ⟨w, hw⟩ : ∃ w, (alg.sent I A.F (alg.exec f I ρ A k₀) q p)[0]? = some w :=
    ⟨_, List.getElem?_eq_getElem hlen⟩
  have hw1 : w.1 = 1 := by
    have hw' := hw
    simp only [sent, hq, ite_false] at hw'
    obtain ⟨h, x, -, -, rfl⟩ := alg.outbox_getElem q (I q) _ 0 w hw'
    rfl
  obtain ⟨k, -, hk⟩ := alg.exists_recv_of_fair f I ρ A hfair hp q hw
  exact ⟨k, mem_senders.2 ⟨w.2, hw1 ▸ hk⟩⟩

/-- In a fair execution, every correct process eventually holds round-1 messages of all correct
processes. -/
theorem exists_senders_one_of_fair (A : Adversary n R M) (hfair : alg.Fair f I ρ A) {p : Fin n}
    (hp : p ∉ A.F) : ∃ k, ∀ q ∉ A.F, q ∈ senders 1 ((alg.exec f I ρ A k).log p) := by
  have : ∀ q, ∃ k, q ∉ A.F → q ∈ senders 1 ((alg.exec f I ρ A k).log p) := by
    intro q
    by_cases hq : q ∈ A.F
    · exact ⟨0, fun h => absurd hq h⟩
    · obtain ⟨k, hk⟩ := alg.exists_recv_one_of_fair f I ρ A hfair hp hq
      exact ⟨k, fun _ => hk⟩
  choose kq hkq using this
  exact ⟨Finset.univ.sup kq, fun q hq =>
    senders_mono ((alg.le_exec f I ρ A (Finset.le_sup (Finset.mem_univ q))).log p) (hkq q hq)⟩

/-- **Round-1 liveness of the canonical-round model.** In a fair execution with at most `f`
faults, every correct process `p` eventually has a history prefix of round `≤ 1` whose
communication-closed view contains round-1 messages from `n - f` distinct senders. -/
theorem exists_ccQuorum_one_of_fair (A : Adversary n R M) (hfair : alg.Fair f I ρ A)
    (hF : A.F.card ≤ f) {p : Fin n} (hp : p ∉ A.F) :
    ∃ k h, h <+: (alg.exec f I ρ A k).log p ∧ rnd h ≤ 1 ∧
      n - f ≤ (senders 1 (ccView h)).card := by
  obtain ⟨k, hk⟩ := alg.exists_senders_one_of_fair f I ρ A hfair hp
  have hcard : n - f ≤ (senders 1 ((alg.exec f I ρ A k).log p)).card := by
    refine le_trans ?_ (Finset.card_le_card (fun q hq => hk q (Finset.mem_compl.1 hq)))
    rw [Finset.card_compl, Fintype.card_fin]; omega
  exact ⟨k, exists_ccQuorum (alg.wellFormed_exec f I ρ A k p) le_rfl hcard⟩

/-! ### A round-robin adversary is admissible -/

theorem rnd_step_wake {F : Finset (Fin n)} (c : Config n R M) {p : Fin n} (hp : p ∉ F) :
    1 ≤ rnd ((alg.step f I F ρ c (.wake p)).log p) := by
  simp only [step]
  split_ifs with h
  · simp only [Function.update_self]
    exact le_trans (by simp) (rnd_mono (prefix_adv f (ρ p) (c.log p ++ [Entry.draw (ρ p 1)])))
  · have : rnd (c.log p) ≠ 0 := fun h0 => h ⟨hp, h0⟩
    omega

end CanonAlg

/-- The oblivious round-robin adversary with faulty set `F`: at times `0, …, n - 1` it wakes up
the processes `0, …, n - 1`; afterwards it cycles through all links `deliver p q`. Byzantine
processes stay silent. -/
def rrAdv (F : Finset (Fin n)) : Adversary n R M where
  F := F
  ev k _ :=
    if h : k < n then .wake ⟨k, h⟩
    else if h' : 0 < n * n then
      .deliver (finProdFinEquiv.symm ⟨(k - n) % (n * n), Nat.mod_lt _ h'⟩).1
        (finProdFinEquiv.symm ⟨(k - n) % (n * n), Nat.mod_lt _ h'⟩).2
    else .skip

namespace CanonAlg

variable (alg : CanonAlg n V R M O) (f : ℕ) (I : Fin n → V) (ρ : Tape n R)

/-- The round-robin adversary is fair for every algorithm and every tape. -/
theorem rrAdv_fair (F : Finset (Fin n)) : alg.Fair f I ρ (rrAdv F) := by
  refine ⟨fun p hp => ⟨p.val + 1, ?_⟩, fun p _ q k => ?_⟩
  · change 1 ≤ rnd ((alg.step f I F ρ (alg.exec f I ρ (rrAdv F) p.val)
      ((rrAdv F).ev p.val (alg.exec f I ρ (rrAdv F) p.val))).log p)
    have : (rrAdv F).ev p.val (alg.exec f I ρ (rrAdv F) p.val) = (.wake p : Event n M) := by
      simp [rrAdv]
    rw [this]; exact alg.rnd_step_wake f I ρ _ hp
  · have hn : 0 < n * n := Nat.mul_pos p.pos p.pos
    have hk := Nat.le_mul_of_pos_left k hn
    refine ⟨n + n * n * k + (finProdFinEquiv (p, q)).val, by omega, ?_⟩
    have h1 : ¬ (n + n * n * k + (finProdFinEquiv (p, q)).val < n) := by omega
    have h2 : (⟨(n + n * n * k + (finProdFinEquiv (p, q)).val - n) % (n * n),
        Nat.mod_lt _ hn⟩ : Fin (n * n)) = finProdFinEquiv (p, q) := by
      ext
      simp only
      rw [show n + n * n * k + (finProdFinEquiv (p, q)).val - n =
        (finProdFinEquiv (p, q)).val + n * n * k by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (finProdFinEquiv (p, q)).isLt]
    simp only [rrAdv, h1, hn, dite_false, dite_true, h2, Equiv.symm_apply_apply]

/-- The round-robin adversary is admissible as soon as it has at most `f` faulty processes; in
particular every algorithm has admissible executions (with any faulty set of size `≤ f`). -/
theorem rrAdv_admissible {F : Finset (Fin n)} (hF : F.card ≤ f) :
    alg.Admissible f I (rrAdv F) :=
  ⟨hF, fun ρ => alg.rrAdv_fair f I ρ F⟩

/-! ### Round complexity -/

theorem decision_isSome_of_decidesBy {p : Fin n} {v : V} {r : ℕ} {l : Log n R M}
    (h : alg.DecidesBy p v r l) : (alg.decision p v l).isSome := by
  obtain ⟨h', hh, -, hs⟩ := h
  exact List.findSome?_isSome_iff.2 ⟨h', hh, hs⟩

theorem allDecide_of_allDecideBy {A : Adversary n R M} {r : ℕ}
    (h : alg.AllDecideBy f I ρ A r) : alg.AllDecide f I ρ A := fun p hp => by
  obtain ⟨k, hk⟩ := h p hp
  exact ⟨k, alg.decision_isSome_of_decidesBy hk⟩

theorem rounds_le_of_allDecideBy {A : Adversary n R M} {r : ℕ}
    (h : alg.AllDecideBy f I ρ A r) : alg.rounds f I ρ A ≤ r :=
  iInf₂_le r h

/-- A uniform bound on the round complexity bounds the expected round complexity, for every
probability distribution of the tape. -/
theorem expRounds_le_of_rounds_le [MeasurableSpace R] (μ : MeasureTheory.Measure (Tape n R))
    [MeasureTheory.IsProbabilityMeasure μ] {A : Adversary n R M} {r : ℕ}
    (h : ∀ ρ, alg.rounds f I ρ A ≤ r) : alg.expRounds f I μ A ≤ r := by
  calc alg.expRounds f I μ A ≤ ∫⁻ _, (r : ENNReal) ∂μ :=
        MeasureTheory.lintegral_mono fun ρ => by
          simpa using ENat.toENNReal_le.2 (h ρ)
    _ = r := by simp

end CanonAlg

end Cslib.Byzantine.CanonicalRounds
