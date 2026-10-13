/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.CanonicalRounds.Liveness

/-!
# Clean round-by-round schedules

A *clean schedule* is an adversary that runs the system in stages. In stage `r` every correct
process `p` first receives the round-`r` messages of a fixed set `hear p` of `n - f` processes
(which makes it start round `r + 1`), then — from stage `lateFrom` on — one message from every
other process (these messages are *late*: they carry a round label smaller than the current round).
Then every correct process gets a wake-up event (only effective in stage `0`), and finally every
Byzantine process `q ∈ hear p` sends its round-`r+1` message to `p`, with content
`bm (r+1) c q p` computed from the current configuration `c` (full-information adversary).

The executions of such a schedule are described round by round (`clean`): the history of a correct
process after stage `r` is its history after stage `r - 1`, followed by the round-`r` messages of
`hear p` and the next random number, plus late messages that are invisible to the algorithm
(for a communication-closed algorithm) or do not exist yet (stages `< lateFrom`). This is
`stageInv_exec`; it is the formal counterpart of "execution `α` in which processes in `X` receive
the round-`r` messages from `Y` and send their round-`r+1` messages" in indistinguishability
proofs.
-/

@[expose] public section

namespace Cslib.Byzantine.CanonicalRounds

variable {n : ℕ} {V R M O : Type*}

namespace CanonAlg

variable (alg : CanonAlg n V R M O) (f : ℕ) (I : Fin n → V) (F : Finset (Fin n)) (ρ : Tape n R)

/-- Run a list of configuration-dependent events. -/
noncomputable def runList : Config n R M → List (Config n R M → Event n M) → Config n R M
  | c, [] => c
  | c, e :: L => runList (alg.step f I F ρ c (e c)) L

@[simp] theorem runList_nil (c : Config n R M) : alg.runList f I F ρ c [] = c := rfl

@[simp] theorem runList_cons (c : Config n R M) (e) (L : List (Config n R M → Event n M)) :
    alg.runList f I F ρ c (e :: L) = alg.runList f I F ρ (alg.step f I F ρ c (e c)) L := rfl

theorem runList_append (c : Config n R M) (L₁ L₂ : List (Config n R M → Event n M)) :
    alg.runList f I F ρ c (L₁ ++ L₂) = alg.runList f I F ρ (alg.runList f I F ρ c L₁) L₂ := by
  induction L₁ generalizing c with
  | nil => rfl
  | cons e L ih => exact ih _

theorem le_runList (c : Config n R M) (L : List (Config n R M → Event n M)) :
    Le c (alg.runList f I F ρ c L) := by
  induction L generalizing c with
  | nil => exact Le.refl c
  | cons e L ih => exact (alg.le_step f I F ρ c _).trans (ih _)

theorem exec_add (A : Adversary n R M) (a : ℕ) (L : List (Config n R M → Event n M))
    (hL : ∀ i (h : i < L.length), A.ev (a + i) = L[i]) :
    alg.exec f I ρ A (a + L.length) = alg.runList f I A.F ρ (alg.exec f I ρ A a) L := by
  induction L generalizing a with
  | nil => rfl
  | cons e L ih =>
    have h0 := hL 0 (by simp)
    simp only [List.getElem_cons_zero, add_zero] at h0
    rw [List.length_cons, show a + (L.length + 1) = (a + 1) + L.length by omega,
      ih (a + 1) (fun i h => by
        have := hL (i + 1) (by simp; omega)
        simpa [show a + (i + 1) = a + 1 + i by omega] using this)]
    simp [exec, h0]

end CanonAlg

/-! ### Round-level description -/

section Clean

variable (alg : CanonAlg n V R M O) (I : Fin n → V) (F : Finset (Fin n))
  (hear : Fin n → Finset (Fin n)) (byz : ℕ → Fin n → Fin n → M) (ρ : Tape n R)

/-- The processes heard by `p`, in increasing order. -/
noncomputable def hearList (p : Fin n) : List (Fin n) := (List.finRange n).filter (· ∈ hear p)

/-- The history of every process after stage `r` of a clean execution (late messages removed):
`hear p` sends its round-`r` messages, Byzantine processes send `byz r q p`. -/
noncomputable def clean : ℕ → Fin n → Log n R M
  | 0 => fun p => [.draw (ρ p 1)]
  | r + 1 => fun p => clean r p ++ (hearList hear p).map (fun q => .recv q (r + 1)
      (if q ∈ F then byz (r + 1) q p else alg.msg q (I q) (clean r q))) ++ [.draw (ρ p (r + 2))]

/-- The content of the round-`r + 1` message from `q` to `p` in the clean execution. -/
noncomputable def cmsg (r : ℕ) (q p : Fin n) : M :=
  if q ∈ F then byz (r + 1) q p else alg.msg q (I q) (clean alg I F hear byz ρ r q)

theorem clean_succ (r : ℕ) (p : Fin n) :
    clean alg I F hear byz ρ (r + 1) p = clean alg I F hear byz ρ r p ++
      (hearList hear p).map (fun q => .recv q (r + 1) (cmsg alg I F hear byz ρ r q p)) ++
      [.draw (ρ p (r + 2))] := rfl

end Clean

/-! ### The schedule -/

section Schedule

variable (F : Finset (Fin n)) (hear : Fin n → Finset (Fin n))
  (bm : ℕ → Config n R M → Fin n → Fin n → M) (lateFrom : ℕ)

/-- The events of process `p`'s block in stage `r`: timely deliveries from `hear p`, then (from
stage `lateFrom` on) one delivery from every other process. -/
noncomputable def blockEvs (r : ℕ) (p : Fin n) : List (Config n R M → Event n M) :=
  (List.finRange n).map (fun q _ => if q ∈ hear p then .deliver p q else .skip) ++
  (List.finRange n).map (fun q _ => if lateFrom ≤ r ∧ q ∉ hear p then .deliver p q else .skip)

/-- The Byzantine sends of stage `r` towards `p`: round-`r+1` messages. -/
noncomputable def byzEvs (r : ℕ) (p : Fin n) : List (Config n R M → Event n M) :=
  (List.finRange n).map (fun q c =>
    if q ∈ F ∧ q ∈ hear p ∧ p ∉ F then .byz q p (r + 1) (bm (r + 1) c q p) else .skip)

/-- All events of stage `r`. -/
noncomputable def stageEvs (r : ℕ) : List (Config n R M → Event n M) :=
  (List.finRange n).flatMap (blockEvs hear lateFrom r) ++
  (List.finRange n).map (fun p _ => .wake p) ++
  (List.finRange n).flatMap (byzEvs F hear bm r)

/-- The (constant) number of events per stage. -/
def stageLen (n : ℕ) : ℕ := n * (2 * n) + n + n * n

theorem length_stageEvs (r : ℕ) :
    (stageEvs (R := R) F hear bm lateFrom r).length = stageLen n := by
  simp [stageEvs, blockEvs, byzEvs, stageLen, List.length_flatMap, List.sum_replicate]
  ring

/-- The clean-schedule adversary. -/
noncomputable def schedule : Adversary n R M :=
  ⟨F, fun k c => ((stageEvs F hear bm lateFrom (k / stageLen n)).getD (k % stageLen n)
    (fun _ => .skip)) c⟩

variable (alg : CanonAlg n V R M O) (f : ℕ) (I : Fin n → V) (ρ : Tape n R)

theorem schedule_ev (hn : 0 < n) (r i : ℕ) (hi : i < stageLen n) :
    (schedule F hear bm lateFrom).ev (r * stageLen n + i) =
      (stageEvs (R := R) F hear bm lateFrom r)[i]'(by rw [length_stageEvs]; exact hi) := by
  have hS : 0 < stageLen n := by unfold stageLen; positivity
  funext c
  simp only [schedule]
  rw [show (r * stageLen n + i) / stageLen n = r by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hi, zero_add],
      show (r * stageLen n + i) % stageLen n = i by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [length_stageEvs]; exact hi), Option.getD_some]

theorem exec_stage (hn : 0 < n) (r : ℕ) :
    alg.exec f I ρ (schedule F hear bm lateFrom) ((r + 1) * stageLen n) =
      alg.runList f I F ρ (alg.exec f I ρ (schedule F hear bm lateFrom) (r * stageLen n))
        (stageEvs F hear bm lateFrom r) := by
  have := alg.exec_add f I ρ (schedule F hear bm lateFrom) (r * stageLen n)
    (stageEvs F hear bm lateFrom r) (fun i h => by
      rw [schedule_ev F hear bm lateFrom hn r i (by rwa [length_stageEvs] at h)])
  rw [length_stageEvs] at this
  rw [add_mul, one_mul, this]
  rfl

end Schedule

/-! ### Step lemmas -/

section StepLemmas

variable (alg : CanonAlg n V R M O) (f : ℕ) (I : Fin n → V) (F : Finset (Fin n)) (ρ : Tape n R)

/-- Only the history and delivery counters of `p` change. -/
structure Frame (p : Fin n) (c c' : Config n R M) : Prop where
  log : ∀ p', p' ≠ p → c'.log p' = c.log p'
  dlvd : ∀ p', p' ≠ p → c'.dlvd p' = c.dlvd p'
  byzOut : c'.byzOut = c.byzOut

theorem Frame.refl (p : Fin n) (c : Config n R M) : Frame p c c :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem Frame.trans {p : Fin n} {c c' c'' : Config n R M} (h : Frame p c c')
    (h' : Frame p c' c'') : Frame p c c'' :=
  ⟨fun p' hp => (h'.log p' hp).trans (h.log p' hp),
    fun p' hp => (h'.dlvd p' hp).trans (h.dlvd p' hp),
    h'.byzOut.trans h.byzOut⟩

theorem step_deliver_some {c : Config n R M} {p q : Fin n} (hp : p ∉ F) {w : ℕ × M}
    (hw : (alg.sent I F c q p)[c.dlvd p q]? = some w) :
    alg.step f I F ρ c (.deliver p q) =
      { c with
        log := Function.update c.log p (adv f (ρ p) (c.log p ++ [.recv q w.1 w.2]))
        dlvd := Function.update c.dlvd p (Function.update (c.dlvd p) q (c.dlvd p q + 1)) } := by
  simp [CanonAlg.step, hp, hw]

theorem step_deliver_none {c : Config n R M} {p q : Fin n}
    (hw : (alg.sent I F c q p)[c.dlvd p q]? = none) : alg.step f I F ρ c (.deliver p q) = c := by
  simp [CanonAlg.step, hw]

theorem step_deliver_byz {c : Config n R M} {p q : Fin n} (hp : p ∈ F) :
    alg.step f I F ρ c (.deliver p q) = c := by
  simp [CanonAlg.step, hp]

theorem frame_step_deliver (c : Config n R M) (p q : Fin n) :
    Frame p c (alg.step f I F ρ c (.deliver p q)) := by
  by_cases hp : p ∈ F
  · rw [step_deliver_byz alg f I F ρ hp]; exact Frame.refl p c
  · rcases hw : (alg.sent I F c q p)[c.dlvd p q]? with _ | w
    · rw [step_deliver_none alg f I F ρ hw]; exact Frame.refl p c
    · rw [step_deliver_some alg f I F ρ hp hw]
      exact ⟨fun p' h => by simp [h], fun p' h => by simp [h], rfl⟩

theorem step_wake_of_ne {c : Config n R M} {p : Fin n} (h : p ∈ F ∨ rnd (c.log p) ≠ 0) :
    alg.step f I F ρ c (.wake p) = c := by
  simp only [CanonAlg.step]; split_ifs with h'
  · exact absurd h' (by tauto)
  · rfl

theorem getElem?_of_prefix {α : Type*} {l l' : List α} (h : l <+: l') {i : ℕ} {a : α}
    (hi : l[i]? = some a) : l'[i]? = some a := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hi).1, hi]

theorem sent_getElem?_mono {c c' : Config n R M} (h : CanonAlg.Le c c') {q p : Fin n} {i : ℕ}
    {w : ℕ × M} (hw : (alg.sent I F c q p)[i]? = some w) : (alg.sent I F c' q p)[i]? = some w :=
  getElem?_of_prefix (alg.sent_prefix I F h q p) hw

theorem senders_eq_empty {r : ℕ} {l : Log n R M} (h : ∀ q r' m, Entry.recv q r' m ∈ l → r' < r) :
    senders r l = ∅ := by
  ext q; simp only [mem_senders, Finset.notMem_empty, iff_false, not_exists]
  intro m hm; exact (h q r m hm).false

/-- Two prefixes ending with a draw, with the same number of earlier draws, coincide. -/
theorem prefix_draw_unique {l h h' : Log n R M} {x x' : R} (hh : h ++ [.draw x] <+: l)
    (hh' : h' ++ [.draw x'] <+: l) (hr : rnd h = rnd h') : h = h' ∧ x = x' := by
  have key : ∀ {h h' : Log n R M} {x x'}, h ++ [.draw x] <+: h' ++ [.draw x'] → rnd h = rnd h' →
      h = h' ∧ x = x' := by
    intro h h' x x' hp hr
    rcases List.prefix_concat_iff.1 hp with h1 | h1
    · obtain ⟨rfl, h2⟩ := List.append_inj' h1 rfl
      simp only [List.cons.injEq, Entry.draw.injEq, and_true] at h2
      exact ⟨rfl, h2⟩
    · have := rnd_mono h1; simp at this; omega
  rcases le_total (h ++ [Entry.draw x]).length (h' ++ [Entry.draw x']).length with hle | hle
  · exact key (List.prefix_of_prefix_length_le hh hh' hle) hr
  · obtain ⟨h1, h2⟩ := key (List.prefix_of_prefix_length_le hh' hh hle) hr.symm
    exact ⟨h1.symm, h2.symm⟩

end StepLemmas

/-! ### One block -/

section Block

variable (alg : CanonAlg n V R M O) (f : ℕ) (I : Fin n → V) (F : Finset (Fin n)) (ρ : Tape n R)

theorem quorum_iff (l : Log n R M) : Quorum f l ↔ 1 ≤ rnd l ∧ n - f ≤ (senders (rnd l) l).card :=
  Iff.rfl

/-- Timely deliveries that do not complete a quorum. -/
theorem timely_run {p : Fin n} (hp : p ∉ F) (r : ℕ) (m : Fin n → M) :
    ∀ (qs : List (Fin n)) (c : Config n R M), qs.Nodup → rnd (c.log p) = r + 1 →
      (∀ q ∈ qs, q ∉ senders (r + 1) (c.log p)) →
      (senders (r + 1) (c.log p)).card + qs.length < n - f →
      (∀ q ∈ qs, c.dlvd p q = r ∧ (alg.sent I F c q p)[r]? = some (r + 1, m q)) →
      let c' := alg.runList f I F ρ c (qs.map fun q _ => .deliver p q)
      c'.log p = c.log p ++ qs.map (fun q => .recv q (r + 1) (m q)) ∧
      (∀ q ∈ qs, c'.dlvd p q = r + 1) ∧ (∀ q ∉ qs, c'.dlvd p q = c.dlvd p q) ∧
      Frame p c c' ∧ CanonAlg.Le c c'
  | [], c, _, _, _, _, _ => by
    exact ⟨by simp, by simp, fun _ _ => rfl, Frame.refl p c, CanonAlg.Le.refl c⟩
  | q :: qs, c, hnd, hr, hs, hcnt, hpre => by
    obtain ⟨hd, hw0⟩ := hpre q (by simp)
    have hw : (alg.sent I F c q p)[c.dlvd p q]? = some (r + 1, m q) := by rw [hd]; exact hw0
    have hq : q ∉ senders (r + 1) (c.log p) := hs q (by simp)
    set c1 := alg.step f I F ρ c (.deliver p q) with hc1
    have hc1' := step_deliver_some alg f I F ρ hp hw
    have hsend : senders (r + 1) (c.log p ++ [.recv q (r + 1) (m q)]) =
        insert q (senders (r + 1) (c.log p)) := senders_append_recv _ _ _ _
    have hnq : ¬ Quorum f (c.log p ++ [Entry.recv q (r + 1) (m q)]) := by
      rw [quorum_iff]; simp only [rnd_append, rnd_recv, add_zero, hr, hsend,
        Finset.card_insert_of_notMem hq]
      simp at hcnt; omega
    have hlog1 : c1.log p = c.log p ++ [.recv q (r + 1) (m q)] := by
      rw [hc1, hc1']; simp [adv_of_not_quorum hnq]
    have hle1 : CanonAlg.Le c c1 := alg.le_step f I F ρ c _
    have hfr1 : Frame p c c1 := frame_step_deliver alg f I F ρ c p q
    have hdl1 : ∀ q', c1.dlvd p q' = if q' = q then r + 1 else c.dlvd p q' := by
      intro q'; rw [hc1, hc1']; split_ifs with h <;> simp [h, hd]
    simp only [List.nodup_cons] at hnd
    have ih := timely_run hp r m qs c1 hnd.2 (by rw [hlog1]; simp [hr])
      (fun q' hq' => by
        rw [hlog1, hsend, Finset.mem_insert, not_or]
        exact ⟨fun h => hnd.1 (h ▸ hq'), hs q' (by simp [hq'])⟩)
      (by rw [hlog1, hsend, Finset.card_insert_of_notMem hq]; simp at hcnt; omega)
      (fun q' hq' => by
        have hne : q' ≠ q := fun h => hnd.1 (h ▸ hq')
        obtain ⟨h1, h2⟩ := hpre q' (by simp [hq'])
        exact ⟨by rw [hdl1, ite_eq_right hne, h1], sent_getElem?_mono alg I F hle1 h2⟩)
    simp only [List.map_cons, CanonAlg.runList_cons] at ih ⊢
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih
    refine ⟨by rw [i1, hlog1]; simp, ?_, ?_, hfr1.trans i4, hle1.trans i5⟩
    · intro q' hq'
      simp only [List.mem_cons] at hq'
      rcases hq' with rfl | hq'
      · rw [i3 _ hnd.1, hdl1, ite_eq_left rfl]
      · exact i2 q' hq'
    · intro q' hq'
      simp only [List.mem_cons, not_or] at hq'
      rw [i3 q' hq'.2, hdl1, ite_eq_right hq'.1]

/-- The timely delivery completing the quorum: the process starts round `r + 2`. -/
theorem timely_last {p : Fin n} (hp : p ∉ F) (_hf : f < n) (r : ℕ) (q : Fin n) (mq : M)
    (c : Config n R M) (hr : rnd (c.log p) = r + 1) (hq : q ∉ senders (r + 1) (c.log p))
    (hcnt : (senders (r + 1) (c.log p)).card + 1 = n - f)
    (hlab : ∀ q r' m, Entry.recv q r' m ∈ c.log p → r' ≤ r + 1)
    (hd : (alg.sent I F c q p)[c.dlvd p q]? = some (r + 1, mq)) :
    let c' := alg.step f I F ρ c (.deliver p q)
    c'.log p = c.log p ++ [.recv q (r + 1) mq, .draw (ρ p (r + 2))] ∧
      c'.dlvd p q = c.dlvd p q + 1 ∧ (∀ q', q' ≠ q → c'.dlvd p q' = c.dlvd p q') ∧
      Frame p c c' ∧ CanonAlg.Le c c' := by
  have hc1' := step_deliver_some alg f I F ρ hp hd
  have hsend : senders (r + 1) (c.log p ++ [.recv q (r + 1) mq]) =
      insert q (senders (r + 1) (c.log p)) := senders_append_recv _ _ _ _
  have hQ : Quorum f (c.log p ++ [Entry.recv q (r + 1) mq]) := by
    rw [quorum_iff]; simp only [rnd_append, rnd_recv, add_zero, hr, hsend,
      Finset.card_insert_of_notMem hq]
    omega
  have hnQ : ∀ x, ¬ Quorum f (c.log p ++ [Entry.recv q (r + 1) mq] ++ [.draw x]) := by
    intro x
    rw [quorum_iff]
    have : senders (r + 2) (c.log p ++ [Entry.recv q (r + 1) mq] ++ [.draw x]) = ∅ := by
      apply senders_eq_empty
      intro q' r' m' hm
      simp only [List.mem_append, List.mem_singleton, Entry.recv.injEq, reduceCtorEq,
        or_false] at hm
      rcases hm with hm | ⟨-, rfl, -⟩
      · have := hlab q' r' m' hm; omega
      · omega
    simp only [rnd_append, rnd_recv, rnd_draw, hr]
    rw [show r + 1 + 0 + 1 = r + 2 by omega, this]; simp; omega
  refine ⟨?_, ?_, ?_, frame_step_deliver alg f I F ρ c p q, alg.le_step f I F ρ c _⟩
  · rw [hc1']; simp only [Function.update_self]
    rw [adv_of_quorum hQ (hnQ _)]; simp [hr]
  · rw [hc1']; simp
  · intro q' hq'; rw [hc1']; simp [hq']

theorem rnd_eq_zero_of_recv {l : Log n R M} {P : ℕ → Prop}
    (h : ∀ e ∈ l, ∃ q r' m, e = Entry.recv q r' m ∧ P r') : rnd l = 0 := by
  unfold rnd; rw [List.countP_eq_zero]
  intro e he; obtain ⟨q, r', m, rfl, -⟩ := h e he; simp [Entry.isDraw]

/-- Late deliveries (round labels below the current round `k`) do not trigger a new round. -/
theorem late_run {p : Fin n} (hp : p ∉ F) (hf : f < n) (k : ℕ) :
    ∀ (qs : List (Fin n)) (c : Config n R M), qs.Nodup → rnd (c.log p) = k →
      (∀ q r' m, Entry.recv q r' m ∈ c.log p → r' < k) →
      (∀ q ∈ qs, (q ∈ F ∧ c.byzOut q p = []) ∨ (q ∉ F ∧ c.dlvd p q + 1 < k)) →
      let c' := alg.runList f I F ρ c (qs.map fun q _ => .deliver p q)
      (∃ late : Log n R M, c'.log p = c.log p ++ late ∧
        ∀ e ∈ late, ∃ q r' m, e = .recv q r' m ∧ r' < k) ∧
      (∀ q, c'.dlvd p q ≤ c.dlvd p q + if q ∈ qs then 1 else 0) ∧
      Frame p c c' ∧ CanonAlg.Le c c'
  | [], c, _, _, _, _ => by
    exact ⟨⟨[], by simp, by simp⟩, by simp, Frame.refl p c, CanonAlg.Le.refl c⟩
  | q :: qs, c, hnd, hr, hlab, hq => by
    simp only [List.nodup_cons] at hnd
    -- the first step
    have h1 : ∃ c1 : Config n R M, c1 = alg.step f I F ρ c (.deliver p q) := ⟨_, rfl⟩
    obtain ⟨c1, hc1⟩ := h1
    have hle1 : CanonAlg.Le c c1 := hc1 ▸ alg.le_step f I F ρ c _
    have hfr1 : Frame p c c1 := hc1 ▸ frame_step_deliver alg f I F ρ c p q
    have hst : (∃ late : Log n R M, c1.log p = c.log p ++ late ∧
        ∀ e ∈ late, ∃ q r' m, e = .recv q r' m ∧ r' < k) ∧
        c1.dlvd p q ≤ c.dlvd p q + 1 ∧ ∀ q', q' ≠ q → c1.dlvd p q' = c.dlvd p q' := by
      rcases hw : (alg.sent I F c q p)[c.dlvd p q]? with _ | w
      · rw [step_deliver_none alg f I F ρ hw] at hc1; subst hc1
        exact ⟨⟨[], by simp, by simp⟩, by omega, fun _ _ => rfl⟩
      · rw [step_deliver_some alg f I F ρ hp hw] at hc1; subst hc1
        have hwl : w.1 < k := by
          rcases hq q (by simp) with ⟨hF, hb⟩ | ⟨hF, hd⟩
          · simp [CanonAlg.sent, hF, hb] at hw
          · simp only [CanonAlg.sent, hF, ite_false] at hw
            obtain ⟨h, x, -, -, rfl⟩ := alg.outbox_getElem q (I q) _ _ w hw
            simpa using hd
        have hnq : ¬ Quorum f (c.log p ++ [Entry.recv q w.1 w.2]) := by
          rw [quorum_iff]
          rw [show rnd (c.log p ++ [Entry.recv q w.1 w.2]) = k by simp [hr],
            senders_eq_empty (fun q' r' m' hm => by
              simp only [List.mem_append, List.mem_singleton, Entry.recv.injEq] at hm
              rcases hm with hm | ⟨-, rfl, -⟩
              · exact hlab q' r' m' hm
              · exact hwl)]
          simp; omega
        refine ⟨⟨[.recv q w.1 w.2], by simp [adv_of_not_quorum hnq], ?_⟩, by simp, ?_⟩
        · simp only [List.mem_singleton]; rintro e rfl; exact ⟨q, w.1, w.2, rfl, hwl⟩
        · intro q' hq'; simp [hq']
    obtain ⟨⟨late1, hl1, hlate1⟩, hd1, hd1'⟩ := hst
    have ih := late_run hp hf k qs c1 hnd.2
      (by rw [hl1, rnd_append, hr, rnd_eq_zero_of_recv hlate1, add_zero])
      (fun q' r' m' hm => by
        rw [hl1, List.mem_append] at hm
        rcases hm with hm | hm
        · exact hlab q' r' m' hm
        · obtain ⟨_, _, _, he, hlt⟩ := hlate1 _ hm
          cases he; exact hlt)
      (fun q' hq' => by
        have hne : q' ≠ q := fun h => hnd.1 (h ▸ hq')
        rw [hd1' q' hne, show c1.byzOut = c.byzOut from hfr1.byzOut]
        exact hq q' (by simp [hq']))
    simp only [List.map_cons, CanonAlg.runList_cons] at ih ⊢
    rw [← hc1]
    obtain ⟨⟨late2, hl2, hlate2⟩, hd2, hfr2, hle2⟩ := ih
    refine ⟨⟨late1 ++ late2, by rw [hl2, hl1, List.append_assoc], ?_⟩, ?_, hfr1.trans hfr2,
      hle1.trans hle2⟩
    · intro e he; rw [List.mem_append] at he
      rcases he with he | he
      · exact hlate1 e he
      · exact hlate2 e he
    · intro q'
      have := hd2 q'
      by_cases hq' : q' = q
      · subst hq'; simp [hnd.1] at this ⊢; omega
      · rw [hd1' q' hq'] at this
        by_cases hq'' : q' ∈ qs <;> simp [hq', hq''] at this ⊢ <;> omega

@[simp] theorem rnd_map_recv {α : Type*} (qs : List α) (g : α → Fin n) (r : α → ℕ) (m : α → M) :
    rnd (qs.map fun a => (Entry.recv (g a) (r a) (m a) : Entry n R M)) = 0 := by
  simp [rnd, List.countP_map, Function.comp_def, Entry.isDraw]

theorem runList_filter_deliver (p : Fin n) (P : Fin n → Prop) [DecidablePred P] (c : Config n R M)
    (l : List (Fin n)) :
    alg.runList f I F ρ c (l.map fun q _ => if P q then .deliver p q else .skip) =
      alg.runList f I F ρ c ((l.filter fun q => decide (P q)).map fun q _ => .deliver p q) := by
  induction l generalizing c with
  | nil => rfl
  | cons q l ih =>
    by_cases hq : P q
    · simp only [List.map_cons, CanonAlg.runList_cons, hq, ite_true, List.filter_cons,
        decide_true]; exact ih _
    · simp only [List.map_cons, CanonAlg.runList_cons, hq, ite_false, List.filter_cons,
        decide_false]; exact ih _

theorem senders_append_map (r : ℕ) (l : Log n R M) (qs : List (Fin n)) (m : Fin n → M) :
    senders r (l ++ qs.map fun q => Entry.recv q r (m q)) = senders r l ∪ qs.toFinset := by
  ext q
  simp only [mem_senders, List.mem_append, List.mem_map, Entry.recv.injEq, Finset.mem_union,
    List.mem_toFinset]
  constructor
  · rintro ⟨m', h | ⟨q', hq', rfl, -, -⟩⟩
    · exact Or.inl ⟨m', h⟩
    · exact Or.inr hq'
  · rintro (⟨m', h⟩ | h)
    · exact ⟨m', Or.inl h⟩
    · exact ⟨m q, Or.inr ⟨q, h, rfl, trivial, rfl⟩⟩

theorem nodup_hearList (hear : Fin n → Finset (Fin n)) (p : Fin n) : (hearList hear p).Nodup :=
  (List.nodup_finRange n).filter _

theorem mem_hearList {hear : Fin n → Finset (Fin n)} {p q : Fin n} :
    q ∈ hearList hear p ↔ q ∈ hear p := by
  simp [hearList]

theorem length_hearList (hear : Fin n → Finset (Fin n)) (p : Fin n) :
    (hearList hear p).length = (hear p).card := by
  rw [← List.toFinset_card_of_nodup (nodup_hearList hear p)]
  congr 1; ext q; simp [mem_hearList]

/-- A whole block of a correct process `p` in stage `r + 1`. -/
theorem block_run (hear : Fin n → Finset (Fin n)) (lateFrom : ℕ) {p : Fin n} (hp : p ∉ F)
    (hf : f < n) (hcard : (hear p).card = n - f) (r : ℕ) (m : Fin n → M) (c : Config n R M)
    (hr : rnd (c.log p) = r + 1) (hlab : ∀ q r' m, Entry.recv q r' m ∈ c.log p → r' ≤ r)
    (htim : ∀ q ∈ hear p, c.dlvd p q = r ∧ (alg.sent I F c q p)[r]? = some (r + 1, m q))
    (hlt : lateFrom ≤ r + 1 → ∀ q ∉ hear p, (q ∈ F ∧ c.byzOut q p = []) ∨
      (q ∉ F ∧ c.dlvd p q ≤ r)) :
    let c' := alg.runList f I F ρ c (blockEvs hear lateFrom (r + 1) p)
    (∃ late : Log n R M,
      c'.log p = c.log p ++ (hearList hear p).map (fun q => .recv q (r + 1) (m q))
        ++ [.draw (ρ p (r + 2))] ++ late ∧ (∀ e ∈ late, ∃ q r' m, e = .recv q r' m ∧ r' < r + 2) ∧
        (¬ lateFrom ≤ r + 1 → late = [])) ∧
      (∀ q ∈ hear p, c'.dlvd p q = r + 1) ∧
      (∀ q ∉ hear p, c'.dlvd p q ≤ c.dlvd p q + 1 ∧
        (¬ lateFrom ≤ r + 1 → c'.dlvd p q = c.dlvd p q)) ∧
      Frame p c c' ∧ CanonAlg.Le c c' := by
  intro c'
  have hc' : c' = alg.runList f I F ρ (alg.runList f I F ρ c
      ((hearList hear p).map fun q _ => .deliver p q))
      ((List.finRange n).map fun q _ => if lateFrom ≤ r + 1 ∧ q ∉ hear p then .deliver p q
        else .skip) := by
    have e := runList_filter_deliver alg f I F ρ p (fun q => q ∈ hear p) c (List.finRange n)
    simp only [c', blockEvs, CanonAlg.runList_append]
    rw [e]; rfl
  -- timely part
  have hlen : (hearList hear p).length = n - f := by rw [length_hearList, hcard]
  obtain ⟨H', ql, hH⟩ : ∃ H' ql, hearList hear p = H' ++ [ql] := by
    rcases List.eq_nil_or_concat (hearList hear p) with h | ⟨H', ql, h⟩
    · rw [h] at hlen; simp at hlen; omega
    · exact ⟨H', ql, by rw [h, List.concat_eq_append]⟩
  have hnd := nodup_hearList hear p
  rw [hH, List.nodup_append] at hnd
  have hqlH : ql ∉ H' := fun h => hnd.2.2 ql h ql (by simp) rfl
  have hmemH : ∀ q, q ∈ H' ∨ q = ql ↔ q ∈ hear p := by
    intro q; rw [← mem_hearList (hear := hear), hH]; simp
  have hs0 : senders (r + 1) (c.log p) = ∅ :=
    senders_eq_empty fun q r' m hm => by have := hlab q r' m hm; omega
  have hlen' : H'.length + 1 = n - f := by rw [← hlen, hH]; simp
  obtain ⟨t1, t2, t3, t4, t5⟩ := timely_run alg f I F ρ hp r m H' c hnd.1 hr
    (by simp [hs0]) (by rw [hs0]; simp; omega)
    (fun q hq => htim q ((hmemH q).1 (Or.inl hq)))
  set c1 := alg.runList f I F ρ c (H'.map fun q _ => .deliver p q) with hc1
  have hql := htim ql ((hmemH ql).1 (Or.inr rfl))
  obtain ⟨u1, u2, u3, u4, u5⟩ := timely_last alg f I F ρ hp hf r ql (m ql) c1
    (by rw [t1]; simp [hr, rnd_map_recv])
    (by rw [t1, senders_append_map, hs0]; simpa using hqlH)
    (by rw [t1, senders_append_map, hs0]; simp [List.toFinset_card_of_nodup hnd.1]; omega)
    (fun q r' m' hm => by
      rw [t1, List.mem_append] at hm
      rcases hm with hm | hm
      · have := hlab q r' m' hm; omega
      · simp at hm; omega)
    (by rw [t3 ql hqlH, hql.1]; exact sent_getElem?_mono alg I F t5 hql.2)
  set c2 := alg.step f I F ρ c1 (.deliver p ql) with hc2
  have hc2' : alg.runList f I F ρ c ((hearList hear p).map fun q _ => .deliver p q) = c2 := by
    rw [hH, List.map_append, CanonAlg.runList_append]; rfl
  have hlog2 : c2.log p = c.log p ++ (hearList hear p).map (fun q => .recv q (r + 1) (m q))
      ++ [.draw (ρ p (r + 2))] := by
    rw [u1, t1, hH]; simp
  have hdl2 : ∀ q, c2.dlvd p q = if q ∈ hear p then r + 1 else c.dlvd p q := by
    intro q
    by_cases h1 : q = ql
    · subst h1; rw [u2, t3 q hqlH, hql.1, ite_eq_left ((hmemH q).1 (Or.inr rfl))]
    · rw [u3 q h1]
      by_cases h2 : q ∈ H'
      · rw [t2 q h2, ite_eq_left ((hmemH q).1 (Or.inl h2))]
      · rw [t3 q h2, ite_eq_right (fun h => by rcases (hmemH q).2 h with h | h <;> contradiction)]
  have hfr2 : Frame p c c2 := t4.trans u4
  have hle2 : CanonAlg.Le c c2 := t5.trans u5
  rw [hc2'] at hc'
  -- late part
  by_cases hact : lateFrom ≤ r + 1
  · have e := runList_filter_deliver alg f I F ρ p (fun q => lateFrom ≤ r + 1 ∧ q ∉ hear p) c2
      (List.finRange n)
    rw [e] at hc'
    obtain ⟨⟨late, hl, hlate⟩, w2, w3, w4⟩ := late_run alg f I F ρ hp hf (r + 2)
      ((List.finRange n).filter fun q => decide (lateFrom ≤ r + 1 ∧ q ∉ hear p)) c2
      ((List.nodup_finRange n).filter _) (by rw [hlog2]; simp [hr, rnd_map_recv])
      (fun q r' m' hm => by
        rw [hlog2] at hm; simp only [List.mem_append, List.mem_map, List.mem_singleton,
          reduceCtorEq, or_false] at hm
        rcases hm with hm | ⟨q', -, he⟩
        · have := hlab q r' m' hm; omega
        · cases he; omega)
      (fun q hq => by
        simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hq
        rw [hfr2.byzOut, hdl2, ite_eq_right hq.2]
        rcases hlt hact q hq.2 with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, by omega⟩)
    rw [← hc'] at hl w2 w3 w4
    refine ⟨⟨late, by rw [hl, hlog2], hlate, fun h => absurd hact h⟩, ?_, ?_, hfr2.trans w3,
      hle2.trans w4⟩
    · intro q hq
      have h1 := w2 q
      have h2 := w4.dlvd p q
      simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq, hq,
        not_true_eq_false, and_false, ite_false, add_zero] at h1
      rw [hdl2, ite_eq_left hq] at h1 h2
      omega
    · intro q hq
      have h1 := w2 q
      rw [hdl2, ite_eq_right hq] at h1
      refine ⟨by split_ifs at h1 <;> omega, fun h => absurd hact h⟩
  · have e := runList_filter_deliver alg f I F ρ p (fun q => lateFrom ≤ r + 1 ∧ q ∉ hear p) c2
      (List.finRange n)
    rw [e, List.filter_eq_nil_iff.2 (fun q _ => by simp [hact])] at hc'
    simp only [List.map_nil, CanonAlg.runList_nil] at hc'
    rw [hc']
    refine ⟨⟨[], by rw [hlog2, List.append_nil], by simp, fun _ => rfl⟩, fun q hq => by
      rw [hdl2, ite_eq_left hq], fun q hq => by rw [hdl2, ite_eq_right hq]; omega, hfr2, hle2⟩

end Block

/-! ### Phases of a stage -/

section Phases

variable (alg : CanonAlg n V R M O) (f : ℕ) (I : Fin n → V) (F : Finset (Fin n)) (ρ : Tape n R)

theorem runList_id (c : Config n R M) (L : List (Config n R M → Event n M))
    (h : ∀ e ∈ L, alg.step f I F ρ c (e c) = c) : alg.runList f I F ρ c L = c := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [CanonAlg.runList_cons, h e (by simp)]
    exact ih fun e' he' => h e' (by simp [he'])

theorem runList_blockEvs_byz (hear : Fin n → Finset (Fin n)) (lateFrom r : ℕ) {p : Fin n}
    (hp : p ∈ F) (c : Config n R M) : alg.runList f I F ρ c (blockEvs hear lateFrom r p) = c := by
  apply runList_id
  intro e he
  simp only [blockEvs, List.mem_append, List.mem_map, List.mem_finRange, true_and] at he
  rcases he with ⟨q, rfl⟩ | ⟨q, rfl⟩ <;> dsimp only <;> split_ifs <;>
    first | rfl | exact step_deliver_byz alg f I F ρ hp

variable (hear : Fin n → Finset (Fin n)) (lateFrom : ℕ)

/-- The state of a correct process after its block of stage `r + 1`, relative to the
configuration `c0` at the beginning of the stage. -/
def PostBlock (r : ℕ) (m : Fin n → Fin n → M) (c0 c : Config n R M) (p : Fin n) : Prop :=
  (∃ late : Log n R M,
    c.log p = c0.log p ++ (hearList hear p).map (fun q => .recv q (r + 1) (m p q))
      ++ [.draw (ρ p (r + 2))] ++ late ∧ (∀ e ∈ late, ∃ q r' m, e = .recv q r' m ∧ r' < r + 2) ∧
      (¬ lateFrom ≤ r + 1 → late = [])) ∧
    (∀ q ∈ hear p, c.dlvd p q = r + 1) ∧
    (∀ q ∉ hear p, c.dlvd p q ≤ c0.dlvd p q + 1 ∧
      (¬ lateFrom ≤ r + 1 → c.dlvd p q = c0.dlvd p q))

/-- Preconditions of the blocks of stage `r + 1`, at the beginning `c0` of the stage. -/
structure PreBlock (r : ℕ) (m : Fin n → Fin n → M) (c0 : Config n R M) : Prop where
  card : ∀ p ∉ F, (hear p).card = n - f
  rnd : ∀ p ∉ F, rnd (c0.log p) = r + 1
  lab : ∀ p ∉ F, ∀ q r' m, Entry.recv q r' m ∈ c0.log p → r' ≤ r
  tim : ∀ p ∉ F, ∀ q ∈ hear p, c0.dlvd p q = r ∧ (alg.sent I F c0 q p)[r]? = some (r + 1, m p q)
  lt : lateFrom ≤ r + 1 → ∀ p ∉ F, ∀ q ∉ hear p, (q ∈ F ∧ c0.byzOut q p = []) ∨
    (q ∉ F ∧ c0.dlvd p q ≤ r)

theorem phase1 (hf : f < n) (r : ℕ) (m : Fin n → Fin n → M) (c0 : Config n R M)
    (hpre : PreBlock alg f I F hear lateFrom r m c0) :
    ∀ (ps : List (Fin n)) (c : Config n R M), ps.Nodup → CanonAlg.Le c0 c → c.byzOut = c0.byzOut →
      (∀ p ∈ ps, c.log p = c0.log p ∧ c.dlvd p = c0.dlvd p) →
      let c' := alg.runList f I F ρ c (ps.flatMap (blockEvs hear lateFrom (r + 1)))
      CanonAlg.Le c c' ∧ c'.byzOut = c0.byzOut ∧
      (∀ p ∈ ps, p ∉ F → PostBlock ρ hear lateFrom r m c0 c' p) ∧
      (∀ p ∉ ps, c'.log p = c.log p ∧ c'.dlvd p = c.dlvd p)
  | [], c, _, _, hb, _ => ⟨CanonAlg.Le.refl c, hb, by simp, fun _ _ => ⟨rfl, rfl⟩⟩
  | p :: ps, c, hnd, hle, hb, hun => by
    simp only [List.nodup_cons] at hnd
    simp only [List.flatMap_cons, CanonAlg.runList_append]
    obtain ⟨hlp, hdp⟩ := hun p (by simp)
    -- the block of `p`
    obtain ⟨c1, hc1, hle1, hb1, hpost1, hfr1⟩ : ∃ c1, c1 = alg.runList f I F ρ c
        (blockEvs hear lateFrom (r + 1) p) ∧ CanonAlg.Le c c1 ∧ c1.byzOut = c0.byzOut ∧
        (p ∉ F → PostBlock ρ hear lateFrom r m c0 c1 p) ∧ Frame p c c1 := by
      by_cases hp : p ∈ F
      · rw [runList_blockEvs_byz alg f I F ρ hear lateFrom (r + 1) hp]
        exact ⟨c, rfl, CanonAlg.Le.refl c, hb, fun h => absurd hp h, Frame.refl p c⟩
      · obtain ⟨b1, b2, b3, b4, b5⟩ := block_run alg f I F ρ hear lateFrom hp hf (hpre.card p hp) r
          (m p) c (by rw [hlp]; exact hpre.rnd p hp)
          (fun q r' m' hm => hpre.lab p hp q r' m' (hlp ▸ hm))
          (fun q hq => by
            obtain ⟨h1, h2⟩ := hpre.tim p hp q hq
            exact ⟨by rw [hdp]; exact h1, sent_getElem?_mono alg I F hle h2⟩)
          (fun hact q hq => by
            rw [hb, hdp]; exact hpre.lt hact p hp q hq)
        refine ⟨_, rfl, b5, by rw [b4.byzOut, hb], fun _ => ⟨?_, b2, ?_⟩, b4⟩
        · obtain ⟨late, h1, h2, h3⟩ := b1
          exact ⟨late, by rw [h1, hlp], h2, h3⟩
        · intro q hq; rw [← hdp]; exact b3 q hq
    rw [← hc1]
    obtain ⟨i1, i2, i3, i4⟩ := phase1 hf r m c0 hpre ps c1 hnd.2 (hle.trans hle1) hb1
      (fun p' hp' => by
        have hne : p' ≠ p := fun h => hnd.1 (h ▸ hp')
        rw [hfr1.log p' hne, hfr1.dlvd p' hne]; exact hun p' (by simp [hp']))
    refine ⟨hle1.trans i1, i2, ?_, ?_⟩
    · intro p' hp' hpF
      simp only [List.mem_cons] at hp'
      rcases hp' with rfl | hp'
      · obtain ⟨⟨late, h1, h2, h3⟩, h4, h5⟩ := hpost1 hpF
        obtain ⟨e1, e2⟩ := i4 p' hnd.1
        exact ⟨⟨late, by rw [e1, h1], h2, h3⟩, by rw [e2]; exact h4, by rw [e2]; exact h5⟩
      · exact i3 p' hp' hpF
    · intro p' hp'
      simp only [List.mem_cons, not_or] at hp'
      rw [(i4 p' hp'.2).1, (i4 p' hp'.2).2, hfr1.log p' hp'.1, hfr1.dlvd p' hp'.1]
      exact ⟨rfl, rfl⟩

theorem phase2_awake (c : Config n R M) (h : ∀ p ∉ F, rnd (c.log p) ≠ 0) :
    alg.runList f I F ρ c ((List.finRange n).map fun p _ => .wake p) = c := by
  apply runList_id
  intro e he
  simp only [List.mem_map, List.mem_finRange, true_and] at he
  obtain ⟨p, rfl⟩ := he
  exact step_wake_of_ne alg f I F ρ (by by_cases hp : p ∈ F <;> simp_all)

theorem adv_single_draw (hf : f < n) (ρp : ℕ → R) (x : R) :
    adv f ρp ([.draw x] : Log n R M) = [.draw x] := by
  apply adv_of_not_quorum
  rw [quorum_iff, senders_eq_empty (by simp)]
  simp; omega

theorem phase2_init (hf : f < n) :
    ∀ (ps : List (Fin n)) (c : Config n R M), ps.Nodup → (∀ p ∈ ps, c.log p = []) →
      let c' := alg.runList f I F ρ c (ps.map fun p _ => .wake p)
      (∀ p, c'.log p = if p ∈ ps ∧ p ∉ F then [.draw (ρ p 1)] else c.log p) ∧
      c'.dlvd = c.dlvd ∧ c'.byzOut = c.byzOut
  | [], c, _, _ => ⟨by simp, rfl, rfl⟩
  | p :: ps, c, hnd, hc => by
    simp only [List.nodup_cons] at hnd
    simp only [List.map_cons, CanonAlg.runList_cons]
    obtain ⟨c1, hc1, h1, h2, h3⟩ : ∃ c1, c1 = alg.step f I F ρ c (.wake p) ∧
        (∀ p', c1.log p' = if p' = p ∧ p ∉ F then [.draw (ρ p 1)] else c.log p') ∧
        c1.dlvd = c.dlvd ∧ c1.byzOut = c.byzOut := by
      refine ⟨_, rfl, ?_⟩
      have hl : c.log p = [] := hc p (by simp)
      by_cases hp : p ∈ F
      · rw [step_wake_of_ne alg f I F ρ (Or.inl hp)]; exact ⟨fun p' => by simp [hp], rfl, rfl⟩
      · simp only [CanonAlg.step, hp, not_false_eq_true, hl, rnd_nil, and_self, ite_true,
          List.nil_append, adv_single_draw f hf]
        refine ⟨fun p' => ?_, trivial⟩
        by_cases h : p' = p
        · subst h; simp
        · simp [h]
    rw [← hc1]
    obtain ⟨i1, i2, i3⟩ := phase2_init hf ps c1 hnd.2 (fun p' hp' => by
      rw [h1, ite_eq_right (by rintro ⟨rfl, -⟩; exact hnd.1 hp')]; exact hc p' (by simp [hp']))
    refine ⟨fun p' => ?_, i2.trans h2, i3.trans h3⟩
    rw [i1, h1]
    by_cases hp' : p' = p
    · subst hp'; simp [hnd.1]
    · simp [hp']

theorem step_byz {c : Config n R M} {q p : Fin n} (hq : q ∈ F) (r : ℕ) (m : M) :
    alg.step f I F ρ c (.byz q p r m) =
      { c with
        byzOut := Function.update c.byzOut q
          (Function.update (c.byzOut q) p (c.byzOut q p ++ [(r, m)])) } := by
  simp [CanonAlg.step, hq]

/-- Byzantine sends of a stage, as a list of pairs `(receiver, sender)`. -/
theorem phase3_run (cond : Fin n → Fin n → Prop) [∀ p q, Decidable (cond p q)]
    (hcond : ∀ p q, cond p q → q ∈ F) (s : ℕ) (bm' : Config n R M → Fin n → Fin n → M)
    (val : Fin n → Fin n → M) :
    ∀ (L : List (Fin n × Fin n)) (c : Config n R M), L.Nodup →
      (∀ c' : Config n R M, c'.log = c.log → ∀ p q, cond p q → bm' c' q p = val q p) →
      let c' := alg.runList f I F ρ c (L.map fun pq c' =>
        if cond pq.1 pq.2 then .byz pq.2 pq.1 s (bm' c' pq.2 pq.1) else .skip)
      c'.log = c.log ∧ c'.dlvd = c.dlvd ∧
      ∀ q p, c'.byzOut q p = c.byzOut q p ++ if (p, q) ∈ L ∧ cond p q then [(s, val q p)] else []
  | [], c, _, _ => ⟨rfl, rfl, by simp⟩
  | (p, q) :: L, c, hnd, hbm => by
    simp only [List.nodup_cons] at hnd
    simp only [List.map_cons, CanonAlg.runList_cons]
    obtain ⟨c1, hc1, h1, h2, h3⟩ : ∃ c1, c1 = alg.step f I F ρ c
        (if cond p q then .byz q p s (bm' c q p) else .skip) ∧ c1.log = c.log ∧ c1.dlvd = c.dlvd ∧
        ∀ q' p', c1.byzOut q' p' = c.byzOut q' p' ++
          if p' = p ∧ q' = q ∧ cond p q then [(s, val q p)] else [] := by
      refine ⟨_, rfl, ?_⟩
      by_cases hc : cond p q
      · rw [ite_eq_left hc, step_byz alg f I F ρ (hcond p q hc), hbm c rfl p q hc]
        refine ⟨rfl, rfl, fun q' p' => ?_⟩
        by_cases hq' : q' = q
        · subst hq'
          by_cases hp' : p' = p
          · subst hp'; simp [hc]
          · simp [hp']
        · simp [hq']
      · rw [ite_eq_right hc]; exact ⟨rfl, rfl, fun q' p' => by simp [hc]; rfl⟩
    rw [← hc1]
    obtain ⟨i1, i2, i3⟩ := phase3_run cond hcond s bm' val L c1 hnd.2
      (fun c' hc' => hbm c' (hc'.trans h1))
    refine ⟨i1.trans h1, i2.trans h2, fun q' p' => ?_⟩
    rw [i3, h3, List.append_assoc]
    congr 1
    by_cases hpq : p' = p ∧ q' = q
    · obtain ⟨rfl, rfl⟩ := hpq
      simp [hnd.1]
    · have : ¬ ((p', q') = (p, q)) := fun h => hpq (by simpa using h)
      simpa [this, List.mem_cons] using fun h1 h2 => absurd ⟨h1, h2⟩ hpq

theorem flatMap_byzEvs (hear : Fin n → Finset (Fin n)) (bm : ℕ → Config n R M → Fin n → Fin n → M)
    (r : ℕ) : (List.finRange n).flatMap (byzEvs F hear bm r) =
      ((List.finRange n) ×ˢ (List.finRange n)).map fun pq c =>
        if pq.2 ∈ F ∧ pq.2 ∈ hear pq.1 ∧ pq.1 ∉ F then
          .byz pq.2 pq.1 (r + 1) (bm (r + 1) c pq.2 pq.1) else .skip := by
  simp [SProd.sprod, List.product, List.map_flatMap, Function.comp_def]; rfl

end Phases

/-! ### The stage invariant -/

section Invariant

variable (alg : CanonAlg n V R M O) (f : ℕ) (I : Fin n → V) (F : Finset (Fin n))
  (hear : Fin n → Finset (Fin n)) (byz : ℕ → Fin n → Fin n → M) (ρ : Tape n R) (lateFrom : ℕ)
  (vw : Log n R M → Log n R M)

/-- A *view* of histories through which the algorithm's messages factor: it keeps draws and
timely (or early) messages; `id` and `ccView` are the two instances used. -/
structure ViewOK : Prop where
  nil : vw [] = []
  draw : ∀ l x, vw (l ++ [.draw x]) = vw l ++ [.draw x]
  recv : ∀ l q r m, rnd l ≤ r → vw (l ++ [.recv q r m]) = vw l ++ [.recv q r m]
  msg : ∀ p v l l', vw l = vw l' → alg.msg p v l = alg.msg p v l'

/-- The invariant at the end of stage `r` of a clean schedule. -/
structure StageInv (r : ℕ) (c : Config n R M) : Prop where
  view : ∀ p ∉ F, vw (c.log p) = clean alg I F hear byz ρ r p
  round : ∀ p ∉ F, rnd (c.log p) = r + 1
  dlvdH : ∀ p ∉ F, ∀ q ∈ hear p, c.dlvd p q = r
  dlvdL : ∀ p ∉ F, ∀ q ∉ hear p, c.dlvd p q ≤ r + 1 - lateFrom
  lab : ∀ p ∉ F, ∀ q r' m, Entry.recv q r' m ∈ c.log p → r' ≤ r
  hist : ∀ p ∉ F, ∀ j ≤ r, ∃ h x, h ++ [Entry.draw x] <+: c.log p ∧ rnd h = j ∧
    vw (h ++ [.draw x]) = clean alg I F hear byz ρ j p
  byzOut : ∀ q ∈ F, ∀ p, c.byzOut q p = if q ∈ hear p ∧ p ∉ F then
    (List.range (r + 1)).map (fun j => (j + 1, byz (j + 1) q p)) else []
  draws : ∀ p ∉ F, CanonAlg.DrawsOK (ρ p) (c.log p)

variable {alg vw}

theorem ViewOK.append_timely (hv : ViewOK alg vw) (k : ℕ) (m : Fin n → M) :
    ∀ (qs : List (Fin n)) (l : Log n R M), rnd l ≤ k →
      vw (l ++ qs.map fun q => .recv q k (m q)) = vw l ++ qs.map fun q => .recv q k (m q)
  | [], l, _ => by simp
  | q :: qs, l, hl => by
    have ih := hv.append_timely k m qs (l ++ [.recv q k (m q)]) (by simpa using hl)
    rw [List.map_cons, show l ++ Entry.recv q k (m q) :: qs.map (fun q => Entry.recv q k (m q)) =
      (l ++ [.recv q k (m q)]) ++ qs.map (fun q => Entry.recv q k (m q)) by simp, ih,
      hv.recv l q k (m q) hl]
    simp

theorem view_append_late (hdrop : ∀ l q r m, r < rnd l → vw (l ++ [.recv q r m]) = vw l) :
    ∀ (late l : Log n R M), (∀ e ∈ late, ∃ q r' m, e = .recv q r' m ∧ r' < rnd l) →
      vw (l ++ late) = vw l
  | [], l, _ => by simp
  | e :: late, l, h => by
    obtain ⟨q, r', m, rfl, hr⟩ := h e (by simp)
    rw [← List.singleton_append, ← List.append_assoc,
      view_append_late hdrop late _ (fun e' he' => by
        obtain ⟨q, r'', m', rfl, h'⟩ := h e' (by simp [he'])
        exact ⟨q, r'', m', rfl, by simpa using h'⟩),
      hdrop l q r' m hr]

theorem drawsOK_append_recvs {ρp : ℕ → R} :
    ∀ (es l : Log n R M), CanonAlg.DrawsOK ρp l → (∀ e ∈ es, ∃ q r' m, e = .recv q r' m) →
      CanonAlg.DrawsOK ρp (l ++ es)
  | [], l, hl, _ => by simpa using hl
  | e :: es, l, hl, h => by
    obtain ⟨q, r', m, rfl⟩ := h e (by simp)
    rw [← List.singleton_append, ← List.append_assoc]
    exact drawsOK_append_recvs es _ (CanonAlg.drawsOK_snoc hl _ (fun x hx => by cases hx))
      (fun e' he' => h e' (by simp [he']))

variable (alg)

theorem rnd_clean (r : ℕ) (p : Fin n) : rnd (clean alg I F hear byz ρ r p) = r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih => rw [clean_succ]; simp [ih]

variable {alg}

theorem ViewOK.view_clean (hv : ViewOK alg vw) (r : ℕ) (p : Fin n) :
    vw (clean alg I F hear byz ρ r p) = clean alg I F hear byz ρ r p := by
  induction r with
  | zero => change vw ([] ++ [_]) = _; rw [hv.draw, hv.nil]; rfl
  | succ r ih =>
    rw [clean_succ, hv.draw, hv.append_timely _ _ _ _ (by rw [rnd_clean])]
    rw [ih]

theorem StageInv.sent (hv : ViewOK alg vw) {r : ℕ} {c : Config n R M}
    (hinv : StageInv alg I F hear byz ρ lateFrom vw r c) {p q : Fin n} (hp : p ∉ F)
    (hq : q ∈ hear p) :
    (alg.sent I F c q p)[r]? = some (r + 1, cmsg alg I F hear byz ρ r q p) := by
  by_cases hqF : q ∈ F
  · simp only [CanonAlg.sent, hqF, ite_true, hinv.byzOut q hqF p, hq, hp, not_false_eq_true,
      and_self, cmsg]
    simp
  · simp only [CanonAlg.sent, hqF, ite_false]
    have hlen : r < (alg.outbox q (I q) (c.log q)).length := by
      rw [CanonAlg.length_outbox, hinv.round q hqF]; omega
    obtain ⟨w, hw⟩ : ∃ w, (alg.outbox q (I q) (c.log q))[r]? = some w :=
      ⟨_, List.getElem?_eq_getElem hlen⟩
    obtain ⟨h, x, hh, hr, rfl⟩ := alg.outbox_getElem q (I q) _ _ w hw
    obtain ⟨h', x', hh', hr', hv'⟩ := hinv.hist q hqF r le_rfl
    obtain ⟨rfl, rfl⟩ := prefix_draw_unique hh hh' (hr.trans hr'.symm)
    rw [hw, cmsg, ite_eq_right hqF,
      hv.msg q (I q) _ _ (hv'.trans (hv.view_clean I F hear byz ρ r q).symm)]

variable (alg) (bm : ℕ → Config n R M → Fin n → Fin n → M)

/-- The adversary's Byzantine messages agree with the round-level ones as soon as all correct
processes have drawn the random numbers of the rounds so far. -/
def BmOK : Prop :=
  ∀ (s : ℕ) (c : Config n R M), 1 ≤ s →
    (∀ X ∉ F, s ≤ rnd (c.log X) ∧ CanonAlg.DrawsOK (ρ X) (c.log X)) →
    ∀ q ∈ F, ∀ p, q ∈ hear p → p ∉ F → bm s c q p = byz s q p

theorem phase3_stage {s : ℕ} (c : Config n R M) (hbm : BmOK F hear byz ρ bm)
    (hc : ∀ X ∉ F, s + 1 ≤ rnd (c.log X) ∧ CanonAlg.DrawsOK (ρ X) (c.log X)) :
    let c' := alg.runList f I F ρ c ((List.finRange n).flatMap (byzEvs F hear bm s))
    c'.log = c.log ∧ c'.dlvd = c.dlvd ∧ ∀ q p, c'.byzOut q p = c.byzOut q p ++
      if q ∈ F ∧ q ∈ hear p ∧ p ∉ F then [(s + 1, byz (s + 1) q p)] else [] := by
  intro c'
  have := phase3_run alg f I F ρ (fun p q => q ∈ F ∧ q ∈ hear p ∧ p ∉ F) (fun p q h => h.1) (s + 1)
    (bm (s + 1)) (fun q p => byz (s + 1) q p) ((List.finRange n) ×ˢ (List.finRange n)) c
    (List.Nodup.product (List.nodup_finRange n) (List.nodup_finRange n))
    (fun c' hc' p q hpq => hbm (s + 1) c' (by omega) (fun X hX => hc' ▸ hc X hX) q hpq.1 p hpq.2.1
      hpq.2.2)
  simp only [c', flatMap_byzEvs]
  obtain ⟨h1, h2, h3⟩ := this
  refine ⟨h1, h2, fun q p => ?_⟩
  rw [h3]; simp [List.mem_product]

theorem stageInv_succ (hf : f < n) (hlate : 1 ≤ lateFrom) (hv : ViewOK alg vw)
    (hcard : ∀ p ∉ F, (hear p).card = n - f) (hbm : BmOK F hear byz ρ bm) {r : ℕ}
    (hdrop : lateFrom ≤ r + 1 → ∀ l q r' m, r' < rnd l → vw (l ++ [.recv q r' m]) = vw l)
    {c0 : Config n R M} (hinv : StageInv alg I F hear byz ρ lateFrom vw r c0) :
    StageInv alg I F hear byz ρ lateFrom vw (r + 1)
      (alg.runList f I F ρ c0 (stageEvs F hear bm lateFrom (r + 1))) := by
  set m : Fin n → Fin n → M := fun p q => cmsg alg I F hear byz ρ r q p with hm
  have hpre : PreBlock alg f I F hear lateFrom r m c0 :=
    { card := hcard
      rnd := hinv.round
      lab := hinv.lab
      tim := fun p hp q hq =>
        ⟨hinv.dlvdH p hp q hq, StageInv.sent I F hear byz ρ lateFrom hv hinv hp hq⟩
      lt := fun _ p hp q hq => by
        by_cases hqF : q ∈ F
        · left; refine ⟨hqF, ?_⟩; rw [hinv.byzOut q hqF p, ite_eq_right (fun h => hq h.1)]
        · right; refine ⟨hqF, ?_⟩; have := hinv.dlvdL p hp q hq; omega }
  obtain ⟨-, hb1, hpost, -⟩ := phase1 alg f I F ρ hear lateFrom hf r m c0 hpre (List.finRange n) c0
    (List.nodup_finRange n) (CanonAlg.Le.refl c0) rfl (fun _ _ => ⟨rfl, rfl⟩)
  set c1 := alg.runList f I F ρ c0 ((List.finRange n).flatMap (blockEvs hear lateFrom (r + 1)))
    with hc1
  have hpost' : ∀ p ∉ F, PostBlock ρ hear lateFrom r m c0 c1 p := fun p hp => hpost p (by simp) hp
  -- facts about the logs after phase 1
  have hT : ∀ p ∉ F, rnd (c0.log p ++ (hearList hear p).map (fun q => Entry.recv q (r + 1) (m p q)))
      = r + 1 := fun p hp => by simp [hinv.round p hp]
  have hrnd1 : ∀ p ∉ F, rnd (c1.log p) = r + 2 := by
    intro p hp
    obtain ⟨⟨late, hl, hlate, -⟩, -, -⟩ := hpost' p hp
    rw [hl, rnd_append, rnd_append, hT p hp, rnd_eq_zero_of_recv hlate]; simp
  have hdr1 : ∀ p ∉ F, CanonAlg.DrawsOK (ρ p) (c1.log p) := by
    intro p hp
    obtain ⟨⟨late, hl, hlate, -⟩, -, -⟩ := hpost' p hp
    rw [hl]
    refine drawsOK_append_recvs _ _ (CanonAlg.drawsOK_snoc
      (drawsOK_append_recvs _ _ (hinv.draws p hp) (fun e he => by
        simp only [List.mem_map] at he; obtain ⟨q, -, rfl⟩ := he; exact ⟨_, _, _, rfl⟩)) _
      (fun x hx => by cases hx; rw [hT p hp])) (fun e he => by
        obtain ⟨q, r', m', rfl, -⟩ := hlate e he; exact ⟨_, _, _, rfl⟩)
  have hview1 : ∀ p ∉ F,
      vw (c0.log p ++ (hearList hear p).map (fun q => Entry.recv q (r + 1) (m p q))
        ++ [.draw (ρ p (r + 2))]) = clean alg I F hear byz ρ (r + 1) p := by
    intro p hp
    rw [hv.draw, hv.append_timely _ _ _ _ (by rw [hinv.round p hp]), hinv.view p hp, clean_succ]
  -- phase 2
  have hw : alg.runList f I F ρ c1 ((List.finRange n).map fun p _ => .wake p) = c1 :=
    phase2_awake alg f I F ρ c1 (fun p hp => by rw [hrnd1 p hp]; omega)
  -- phase 3
  obtain ⟨h3l, h3d, h3b⟩ := phase3_stage alg f I F hear byz ρ bm (s := r + 1) c1 hbm
    (fun X hX => ⟨by have := hrnd1 X hX; omega, hdr1 X hX⟩)
  simp only [stageEvs, CanonAlg.runList_append, ← hc1, hw]
  set c2 := alg.runList f I F ρ c1 ((List.finRange n).flatMap (byzEvs F hear bm (r + 1)))
  constructor
  · intro p hp
    obtain ⟨⟨late, hl, hlate, hlate0⟩, -, -⟩ := hpost' p hp
    rw [h3l, hl]
    by_cases hact : lateFrom ≤ r + 1
    · rw [view_append_late (hdrop hact) late _ (fun e he => by
        obtain ⟨q, r', m', rfl, h'⟩ := hlate e he
        refine ⟨q, r', m', rfl, ?_⟩; rw [rnd_append, hT p hp, rnd_draw]; omega), hview1 p hp]
    · rw [hlate0 hact, List.append_nil, hview1 p hp]
  · intro p hp; rw [h3l, hrnd1 p hp]
  · intro p hp q hq; rw [h3d]; exact (hpost' p hp).2.1 q hq
  · intro p hp q hq
    rw [h3d]
    have h1 := ((hpost' p hp).2.2 q hq).1
    have h2 := ((hpost' p hp).2.2 q hq).2
    have h0 := hinv.dlvdL p hp q hq
    by_cases hact : lateFrom ≤ r + 1
    · omega
    · rw [h2 hact]; omega
  · intro p hp q r' m' hm'
    rw [h3l] at hm'
    obtain ⟨⟨late, hl, hlate, -⟩, -, -⟩ := hpost' p hp
    rw [hl] at hm'
    simp only [List.mem_append, List.mem_map, List.mem_singleton, reduceCtorEq, or_false] at hm'
    rcases hm' with (hm' | ⟨q', -, he⟩) | hm'
    · have := hinv.lab p hp q r' m' hm'; omega
    · cases he; omega
    · obtain ⟨_, _, _, he, h'⟩ := hlate _ hm'; cases he; omega
  · intro p hp j hj
    rw [h3l]
    obtain ⟨⟨late, hl, -, -⟩, -, -⟩ := hpost' p hp
    rw [hl]
    rcases Nat.lt_or_ge j (r + 1) with hj' | hj'
    · obtain ⟨h, x, hh, hr, hvv⟩ := hinv.hist p hp j (by omega)
      refine ⟨h, x, hh.trans ?_, hr, hvv⟩
      simp only [List.append_assoc]; exact List.prefix_append _ _
    · refine ⟨c0.log p ++ (hearList hear p).map (fun q => Entry.recv q (r + 1) (m p q)),
        ρ p (r + 2), ?_, by rw [hT p hp]; omega, by rw [show j = r + 1 by omega, hview1 p hp]⟩
      exact List.prefix_append _ _
  · intro q hq p
    rw [h3b, hb1, hinv.byzOut q hq p]
    by_cases hc : q ∈ hear p ∧ p ∉ F
    · simp [hc, hq, List.range_succ]
    · simp [hc, hq]
  · intro p hp; rw [h3l]; exact hdr1 p hp

theorem sent_init (q p : Fin n) : alg.sent I F (Config.init : Config n R M) q p = [] := by
  unfold CanonAlg.sent; split_ifs
  · rfl
  · exact alg.outbox_nil q (I q)

theorem stageInv_zero (hf : f < n) (hlate : 1 ≤ lateFrom) (hv : ViewOK alg vw)
    (hbm : BmOK F hear byz ρ bm) :
    StageInv alg I F hear byz ρ lateFrom vw 0
      (alg.runList f I F ρ Config.init (stageEvs F hear bm lateFrom 0)) := by
  have h1 : alg.runList f I F ρ Config.init ((List.finRange n).flatMap (blockEvs hear lateFrom 0)) =
      Config.init := by
    apply runList_id
    intro e he
    simp only [List.mem_flatMap, List.mem_finRange, true_and, blockEvs, List.mem_append,
      List.mem_map] at he
    obtain ⟨p, ⟨q, rfl⟩ | ⟨q, rfl⟩⟩ := he
    · dsimp only; split_ifs
      · by_cases hp : p ∈ F
        · exact step_deliver_byz alg f I F ρ hp
        · exact step_deliver_none alg f I F ρ (by rw [sent_init]; rfl)
      · rfl
    · dsimp only; rw [ite_eq_right (by omega)]; rfl
  obtain ⟨w1, w2, w3⟩ := phase2_init alg f I F ρ hf (List.finRange n) Config.init
    (List.nodup_finRange n) (fun _ _ => rfl)
  set c1 := alg.runList f I F ρ Config.init ((List.finRange n).map fun p _ => .wake p) with hc1
  have hl1 : ∀ p ∉ F, c1.log p = [.draw (ρ p 1)] := fun p hp => by rw [w1]; simp [hp]
  have hdr1 : ∀ p ∉ F, CanonAlg.DrawsOK (ρ p) (c1.log p) := by
    intro p hp; rw [hl1 p hp]
    exact CanonAlg.drawsOK_snoc (l := []) (fun h x hh => by simpa using hh.length_le) _
      (fun x hx => by cases hx; rfl)
  obtain ⟨h3l, h3d, h3b⟩ := phase3_stage alg f I F hear byz ρ bm (s := 0) c1 hbm
    (fun X hX => ⟨by rw [hl1 X hX]; rfl, hdr1 X hX⟩)
  simp only [stageEvs, CanonAlg.runList_append, h1, ← hc1]
  constructor
  · intro p hp; rw [h3l, hl1 p hp]
    change vw ([] ++ [_]) = _; rw [hv.draw, hv.nil]; rfl
  · intro p hp; rw [h3l, hl1 p hp]; rfl
  · intro p hp q _; rw [h3d, w2]; rfl
  · intro p hp q _; rw [h3d, w2]; exact Nat.zero_le _
  · intro p hp q r' m hm; rw [h3l, hl1 p hp] at hm; simp at hm
  · intro p hp j hj
    obtain rfl : j = 0 := by omega
    refine ⟨[], ρ p 1, by rw [h3l, hl1 p hp]; rfl, rfl, ?_⟩
    rw [hv.draw, hv.nil]; rfl
  · intro q hq p
    rw [h3b, w3]
    by_cases hc : q ∈ hear p ∧ p ∉ F <;> simp [hc, hq, Config.init]
  · intro p hp; rw [h3l]; exact hdr1 p hp

/-- **The stage invariant along a clean schedule**: at the end of every stage `r ≤ rmax`
(`rmax` arbitrary if late messages are invisible to `vw`), the views of the histories of the
correct processes are the round-level histories `clean`. -/
theorem stageInv_exec (hf : f < n) (hlate : 1 ≤ lateFrom) (hv : ViewOK alg vw)
    (hcard : ∀ p ∉ F, (hear p).card = n - f) (hbm : BmOK F hear byz ρ bm) (rmax : ℕ)
    (hdrop : lateFrom ≤ rmax → ∀ l q r' m, r' < rnd l → vw (l ++ [.recv q r' m]) = vw l) :
    ∀ r ≤ rmax, StageInv alg I F hear byz ρ lateFrom vw r
      (alg.exec f I ρ (schedule F hear bm lateFrom) ((r + 1) * stageLen n)) := by
  have hn : 0 < n := by omega
  intro r hr
  induction r with
  | zero =>
    rw [exec_stage F hear bm lateFrom alg f I ρ hn 0]
    simpa [CanonAlg.exec] using stageInv_zero alg f I F hear byz ρ lateFrom bm hf hlate hv hbm
  | succ r ih =>
    rw [exec_stage F hear bm lateFrom alg f I ρ hn (r + 1)]
    exact stageInv_succ alg f I F hear byz ρ lateFrom bm hf hlate hv hcard hbm
      (fun h => hdrop (by omega)) (ih (by omega))

end Invariant

/-! ### Views and fairness -/

section Views

variable (alg : CanonAlg n V R M O)

/-- Full histories (no information is hidden from the algorithm). -/
theorem viewOK_id : ViewOK alg id :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ h => by simp only [id] at h; rw [h]⟩

/-- The communication-closed view, for a communication-closed algorithm. -/
theorem viewOK_cc (h : alg.CommClosed) : ViewOK alg ccView :=
  ⟨rfl, fun l x => by rw [ccView_append_singleton]; rfl,
    fun l q r m hr => by
      rw [ccView_append_singleton]; simp only [ccStep, rnd_ccView, hr, ite_true],
    fun p v l l' hl => (h p v l l' hl).1⟩

theorem ccView_drop (l : Log n R M) (q : Fin n) (r : ℕ) (m : M) (hr : r < rnd l) :
    ccView (l ++ [.recv q r m]) = ccView l := by
  rw [ccView_append_singleton]; simp only [ccStep, rnd_ccView]
  rw [ite_eq_right (by omega)]

end Views

section Fair

variable (alg : CanonAlg n V R M O) (f : ℕ) (I : Fin n → V) (F : Finset (Fin n))
  (hear : Fin n → Finset (Fin n)) (bm : ℕ → Config n R M → Fin n → Fin n → M) (lateFrom : ℕ)
  (ρ : Tape n R)

theorem schedule_deliver_often (hn : 0 < n) (p q : Fin n) (k : ℕ) :
    ∃ k' ≥ k, (schedule F hear bm lateFrom).ev k'
      (alg.exec f I ρ (schedule F hear bm lateFrom) k') = .deliver p q := by
  set r := k + lateFrom
  have hS : 1 ≤ stageLen n := by unfold stageLen; nlinarith
  obtain ⟨e, he, hev⟩ : ∃ e ∈ stageEvs (R := R) F hear bm lateFrom r,
      ∀ c, e c = .deliver p q := by
    by_cases hq : q ∈ hear p
    · refine ⟨fun _ => if q ∈ hear p then .deliver p q else .skip, ?_, fun c => by simp [hq]⟩
      simp only [stageEvs, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
        blockEvs, List.mem_map]
      exact Or.inl (Or.inl ⟨p, Or.inl ⟨q, rfl⟩⟩)
    · refine ⟨fun _ => if lateFrom ≤ r ∧ q ∉ hear p then .deliver p q else .skip, ?_,
        fun c => by simp [hq, r]⟩
      simp only [stageEvs, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
        blockEvs, List.mem_map]
      exact Or.inl (Or.inl ⟨p, Or.inr ⟨q, rfl⟩⟩)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have hi' : i < stageLen n := by rwa [length_stageEvs] at hi
  refine ⟨r * stageLen n + i, ?_, ?_⟩
  · have : k ≤ r * stageLen n := by
      calc k ≤ r := by omega
        _ = r * 1 := by ring
        _ ≤ r * stageLen n := Nat.mul_le_mul_left _ hS
    omega
  · rw [schedule_ev F hear bm lateFrom hn r i hi']; exact hev _

/-- Clean schedules are fair, hence admissible when `|F| ≤ f`. -/
theorem schedule_admissible (hf : f < n) (hlate : 1 ≤ lateFrom) (hFf : F.card ≤ f)
    (hcard : ∀ p ∉ F, (hear p).card = n - f)
    (byz : Tape n R → ℕ → Fin n → Fin n → M) (hbm : ∀ ρ, BmOK F hear (byz ρ) ρ bm) :
    alg.Admissible f I (schedule F hear bm lateFrom) := by
  have hn : 0 < n := by omega
  refine ⟨hFf, fun ρ => ⟨fun p hp => ⟨1 * stageLen n, ?_⟩,
    fun p _ q k => schedule_deliver_often alg f I F hear bm lateFrom ρ hn p q k⟩⟩
  have := stageInv_exec alg f I F hear (byz ρ) ρ lateFrom bm hf hlate (viewOK_id alg) hcard
    (hbm ρ) 0 (fun h => by omega) 0 le_rfl
  rw [this.round p hp]

end Fair

end Cslib.Byzantine.CanonicalRounds
