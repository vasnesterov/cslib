/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.CanonicalRounds.Model

/-!
# Basic lemmas about the canonical-round model

Rounds and outboxes of histories, the cascade `adv`, monotonicity of executions (histories, sent
messages and delivery counters only grow), and the fact that the random numbers in a correct
process' history are read from its row of the tape.
-/

@[expose] public section

namespace Cslib.Byzantine.CanonicalRounds

variable {n : ℕ} {V R M O : Type*}

/-! ### Rounds -/

@[simp] theorem rnd_nil : rnd ([] : Log n R M) = 0 := rfl

@[simp] theorem rnd_append (l l' : Log n R M) : rnd (l ++ l') = rnd l + rnd l' := by
  simp [rnd, List.countP_append]

@[simp] theorem rnd_draw (x : R) : rnd ([.draw x] : Log n R M) = 1 := rfl

@[simp] theorem rnd_recv (q : Fin n) (r : ℕ) (m : M) : rnd ([.recv q r m] : Log n R M) = 0 := rfl

theorem rnd_mono {l l' : Log n R M} (h : l <+: l') : rnd l ≤ rnd l' := by
  obtain ⟨t, rfl⟩ := h; simp

theorem mem_senders {r : ℕ} {l : Log n R M} {q : Fin n} :
    q ∈ senders r l ↔ ∃ m, Entry.recv q r m ∈ l := by
  simp [senders]

theorem senders_mono {r : ℕ} {l l' : Log n R M} (h : l <+: l') : senders r l ⊆ senders r l' := by
  intro q hq
  rw [mem_senders] at hq ⊢
  obtain ⟨m, hm⟩ := hq
  exact ⟨m, h.subset hm⟩

theorem senders_append_draw (r : ℕ) (l : Log n R M) (x : R) :
    senders r (l ++ [.draw x]) = senders r l := by
  ext q; simp [mem_senders]

theorem senders_append_recv_of_ne (r : ℕ) (l : Log n R M) (q : Fin n) (r' : ℕ) (m : M)
    (h : r' ≠ r) : senders r (l ++ [.recv q r' m]) = senders r l := by
  ext q'; simp only [mem_senders, List.mem_append, List.mem_singleton, Entry.recv.injEq]
  constructor
  · rintro ⟨m', h' | ⟨-, rfl, -⟩⟩
    · exact ⟨m', h'⟩
    · exact absurd rfl h
  · rintro ⟨m', h'⟩; exact ⟨m', Or.inl h'⟩

theorem senders_append_recv (r : ℕ) (l : Log n R M) (q : Fin n) (m : M) :
    senders r (l ++ [.recv q r m]) = insert q (senders r l) := by
  ext q'
  simp only [mem_senders, List.mem_append, List.mem_singleton, Entry.recv.injEq,
    Finset.mem_insert]
  constructor
  · rintro ⟨m', h | ⟨rfl, -, -⟩⟩
    · exact Or.inr ⟨m', h⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨m', h⟩)
    · exact ⟨m, Or.inr ⟨rfl, trivial, rfl⟩⟩
    · exact ⟨m', Or.inl h⟩

/-! ### The cascade -/

theorem prefix_advance (f : ℕ) (ρp : ℕ → R) :
    ∀ (k : ℕ) (l : Log n R M), l <+: advance f ρp k l
  | 0, l => List.prefix_refl l
  | k + 1, l => by
    unfold advance
    split_ifs
    · exact (List.prefix_append l _).trans (prefix_advance f ρp k _)
    · exact List.prefix_refl l

theorem prefix_adv (f : ℕ) (ρp : ℕ → R) (l : Log n R M) : l <+: adv f ρp l :=
  prefix_advance f ρp _ l

theorem adv_of_not_quorum {f : ℕ} {ρp : ℕ → R} {l : Log n R M} (h : ¬ Quorum f l) :
    adv f ρp l = l := by
  unfold adv advance; simp [h]

theorem adv_of_quorum {f : ℕ} {ρp : ℕ → R} {l : Log n R M} (h : Quorum f l)
    (h' : ¬ Quorum f (l ++ [.draw (ρp (rnd l + 1))])) :
    adv f ρp l = l ++ [.draw (ρp (rnd l + 1))] := by
  unfold adv advance
  simp only [h, ite_true]
  cases hk : l.length with
  | zero => unfold advance; simp
  | succ k => unfold advance; simp [h']

/-! ### Outboxes -/

namespace CanonAlg

variable (alg : CanonAlg n V R M O)

theorem outbox_nil (q : Fin n) (v : V) : alg.outbox q v [] = [] := by
  simp [outbox]

theorem outbox_append_recv (q : Fin n) (v : V) (l : Log n R M) (q' : Fin n) (r : ℕ) (m : M) :
    alg.outbox q v (l ++ [.recv q' r m]) = alg.outbox q v l := by
  simp [outbox, List.inits_append, Entry.isDraw]

theorem outbox_append_draw (q : Fin n) (v : V) (l : Log n R M) (x : R) :
    alg.outbox q v (l ++ [.draw x]) =
      alg.outbox q v l ++ [(rnd l + 1, alg.msg q v (l ++ [.draw x]))] := by
  simp [outbox, List.inits_append, Entry.isDraw]

theorem outbox_prefix (q : Fin n) (v : V) {l l' : Log n R M} (h : l <+: l') :
    alg.outbox q v l <+: alg.outbox q v l' := by
  obtain ⟨t, rfl⟩ := h
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t e ih =>
    rw [← List.append_assoc]
    refine ih.trans ?_
    cases e with
    | recv q' r m => rw [outbox_append_recv]
    | draw x => rw [outbox_append_draw]; exact List.prefix_append _ _

theorem length_outbox (q : Fin n) (v : V) (l : Log n R M) : (alg.outbox q v l).length = rnd l := by
  induction l using List.reverseRecOn with
  | nil => simp [outbox_nil]
  | append_singleton t e ih =>
    cases e with
    | recv q' r m => rw [outbox_append_recv]; simp [ih]
    | draw x => rw [outbox_append_draw]; simp [ih]

/-- The `i`-th message sent by a correct process has round label `i + 1` and is computed from a
history prefix with `i + 1` draws that ends with a draw. -/
theorem outbox_getElem (q : Fin n) (v : V) (l : Log n R M) (i : ℕ) (w : ℕ × M)
    (hw : (alg.outbox q v l)[i]? = some w) :
    ∃ h x, h ++ [.draw x] <+: l ∧ rnd h = i ∧ w = (i + 1, alg.msg q v (h ++ [.draw x])) := by
  induction l using List.reverseRecOn generalizing w with
  | nil => simp [outbox_nil] at hw
  | append_singleton t e ih =>
    cases e with
    | recv q' r m =>
      rw [outbox_append_recv] at hw
      obtain ⟨h, x, hh, hr, rfl⟩ := ih w hw
      exact ⟨h, x, hh.trans (List.prefix_append _ _), hr, rfl⟩
    | draw x =>
      rw [outbox_append_draw, List.getElem?_append] at hw
      split_ifs at hw with hi
      · obtain ⟨h, x', hh, hr, rfl⟩ := ih w hw
        exact ⟨h, x', hh.trans (List.prefix_append _ _), hr, rfl⟩
      · rw [length_outbox] at hi hw
        rw [List.getElem?_singleton] at hw
        split_ifs at hw with hi'
        · simp only [Option.some.injEq] at hw; subst hw
          refine ⟨t, x, List.prefix_refl _, by omega, ?_⟩
          rw [show i = rnd t by omega]

end CanonAlg

/-! ### Monotonicity of executions -/

namespace CanonAlg

variable (alg : CanonAlg n V R M O) (f : ℕ) (I : Fin n → V) (F : Finset (Fin n)) (ρ : Tape n R)

/-- `c ≤ c'`: histories and Byzantine outboxes are prefixes, delivery counters are smaller. -/
structure Le (c c' : Config n R M) : Prop where
  log : ∀ p, c.log p <+: c'.log p
  byzOut : ∀ q p, c.byzOut q p <+: c'.byzOut q p
  dlvd : ∀ p q, c.dlvd p q ≤ c'.dlvd p q

theorem Le.refl (c : Config n R M) : Le c c := ⟨fun _ => List.prefix_refl _,
  fun _ _ => List.prefix_refl _, fun _ _ => le_rfl⟩

theorem Le.trans {c c' c'' : Config n R M} (h : Le c c') (h' : Le c' c'') : Le c c'' :=
  ⟨fun p => (h.log p).trans (h'.log p), fun q p => (h.byzOut q p).trans (h'.byzOut q p),
    fun p q => (h.dlvd p q).trans (h'.dlvd p q)⟩

theorem sent_prefix {c c' : Config n R M} (h : Le c c') (q p : Fin n) :
    alg.sent I F c q p <+: alg.sent I F c' q p := by
  unfold sent; split_ifs
  · exact h.byzOut q p
  · exact alg.outbox_prefix q (I q) (h.log q)

theorem le_step (c : Config n R M) (e : Event n M) : Le c (alg.step f I F ρ c e) := by
  cases e with
  | wake p =>
    simp only [step]; split_ifs
    · refine ⟨fun p' => ?_, fun _ _ => List.prefix_refl _, fun _ _ => le_rfl⟩
      rcases eq_or_ne p' p with rfl | h
      · simp only [Function.update_self]
        exact (List.prefix_append _ _).trans (prefix_adv _ _ _)
      · simp [h]
    · exact Le.refl c
  | deliver p q =>
    simp only [step]; split_ifs
    · exact Le.refl c
    · split
      · refine ⟨fun p' => ?_, fun _ _ => List.prefix_refl _, fun p' q' => ?_⟩
        · rcases eq_or_ne p' p with rfl | h
          · simp only [Function.update_self]
            exact (List.prefix_append _ _).trans (prefix_adv _ _ _)
          · simp [h]
        · rcases eq_or_ne p' p with rfl | h
          · rcases eq_or_ne q' q with rfl | h'
            · simp
            · simp [h']
          · simp [h]
      · exact Le.refl c
  | byz q p r m =>
    simp only [step]; split_ifs
    · refine ⟨fun _ => List.prefix_refl _, fun q' p' => ?_, fun _ _ => le_rfl⟩
      rcases eq_or_ne q' q with rfl | h
      · rcases eq_or_ne p' p with rfl | h'
        · simp
        · simp [h']
      · simp [h]
    · exact Le.refl c
  | skip => exact Le.refl c

theorem le_exec (A : Adversary n R M) {k k' : ℕ} (h : k ≤ k') :
    Le (alg.exec f I ρ A k) (alg.exec f I ρ A k') := by
  induction h with
  | refl => exact Le.refl _
  | step _ ih => exact ih.trans (alg.le_step f I A.F ρ _ _)

/-- Every random number in the history of a correct process comes from its row of the tape: the
draw ending a prefix with `j` earlier draws is `ρ p (j + 1)`. -/
def DrawsOK (ρp : ℕ → R) (l : Log n R M) : Prop :=
  ∀ h x, h ++ [Entry.draw x] <+: l → x = ρp (rnd h + 1)

theorem drawsOK_snoc {ρp : ℕ → R} {l : Log n R M} (hl : DrawsOK ρp l) (e : Entry n R M)
    (he : ∀ x, e = .draw x → x = ρp (rnd l + 1)) : DrawsOK ρp (l ++ [e]) := by
  intro h x hh
  rcases List.prefix_concat_iff.1 hh with h1 | h1
  · obtain ⟨rfl, h2⟩ := List.append_inj' h1 rfl
    simp only [List.cons.injEq, and_true] at h2
    exact he x h2.symm
  · exact hl h x h1

theorem drawsOK_advance {f : ℕ} {ρp : ℕ → R} :
    ∀ (k : ℕ) {l : Log n R M}, DrawsOK ρp l → DrawsOK ρp (advance f ρp k l)
  | 0, l, hl => hl
  | k + 1, l, hl => by
    unfold advance
    split_ifs
    · exact drawsOK_advance k (drawsOK_snoc hl _ fun x hx => by cases hx; rfl)
    · exact hl

theorem drawsOK_adv {f : ℕ} {ρp : ℕ → R} {l : Log n R M} (hl : DrawsOK ρp l) (e : Entry n R M)
    (he : ∀ x, e = .draw x → x = ρp (rnd l + 1)) : DrawsOK ρp (adv f ρp (l ++ [e])) :=
  drawsOK_advance _ (drawsOK_snoc hl e he)

theorem drawsOK_exec (A : Adversary n R M) (k : ℕ) (p : Fin n) :
    DrawsOK (ρ p) ((alg.exec f I ρ A k).log p) := by
  induction k with
  | zero => intro h x hh; simpa [exec, Config.init] using hh.length_le
  | succ k ih =>
    simp only [exec]
    generalize A.ev k (alg.exec f I ρ A k) = e
    generalize alg.exec f I ρ A k = c at ih
    cases e with
    | wake p' =>
      simp only [step]; split_ifs with hw
      · rcases eq_or_ne p p' with rfl | hne
        · simp only [Function.update_self]
          exact drawsOK_adv ih _ (fun x hx => by cases hx; rw [hw.2])
        · simpa [hne] using ih
      · exact ih
    | deliver p' q =>
      simp only [step]; split_ifs
      · exact ih
      · split
        · rcases eq_or_ne p p' with rfl | hne
          · simp only [Function.update_self]
            exact drawsOK_adv ih _ (fun x hx => by cases hx)
          · simpa [hne] using ih
        · exact ih
    | byz q p' r m => simp only [step]; split_ifs <;> exact ih
    | skip => exact ih

end CanonAlg

end Cslib.Byzantine.CanonicalRounds
