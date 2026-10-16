/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.LockStep.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Order.SuccPred.Nat

/-!
# The synchronous crash-failure model (`γ_f`), knowledge and message chains

The standard synchronous message-passing model with crash failures, as used e.g. by Goren and
Moses [GorenMoses2018] (§2.2), Dwork–Moses, Hadzilacos, and Guerraoui–Wang:

* a complete network of processes `P`, synchronous rounds; round `t + 1` takes place between
  time `t` and time `t + 1` (a message *sent at time `t`* is received at time `t + 1`);
* protocols are deterministic and **history based**: we reuse CSLib's lock-step protocols
  `Cslib.Byzantine.LockStep.Protocol P I M O` (`send p x h q`, `decide p x h`, where `x` is the
  input and `h` the list of inboxes received so far), so the local state of `p` at time `m` is
  `(input, history of length m)`; the messages a process has sent are a function of this, and
  the time is the length of the history;
* a run is given by the inputs and the **crash pattern** (`Run`): `crash p = some c` means `p`
  crashes in round `c ≥ 1`: it behaves correctly in rounds `< c`, in round `c` it sends its
  prescribed messages only to the processes in `reach p`, and from time `c` on its local state is
  `⊥` (`state … = none`); `crash p = none` means `p` is correct;
* `Run.Admissible f`: at most `f` processes crash (the model `γ_f`); the system `R(P, γ_f)` is the
  set of admissible runs of `alg`;
* **knowledge** is defined semantically (`Knows`): `K_i φ` holds at time `m` of `r` iff `φ` holds in
  every admissible run `r'` with `r'_i(m) = r_i(m)`;
* message chains (`Chain`), the set of messages of a run (`msgs`, counted with `Set.encard`).

Runs are computed with CSLib's lock-step semantics (`Cslib.Byzantine.LockStep.hist`) on the complete
graph, with no Byzantine parties and with the crash pattern encoded as message omissions
(`Run.toScenario`); the crash model adds the `⊥` states on top.

Self-messages do not exist (the complete `SimpleGraph` has no loops): protocols use their own state
instead, and message counts never include messages to oneself.

## References

* [G. Goren, Y. Moses, *Silence*][GorenMoses2018]
-/

@[expose] public section

namespace Cslib.SyncCrash

variable {P I M O : Type*}

/-- The data of a run: inputs and crash pattern. `crash p = some c`: `p` crashes in round `c`
(only meaningful for `c ≥ 1`, see `Admissible`), sending its round-`c` messages only to `reach p`.
-/
structure Run (P I : Type*) where
  /-- Initial values. -/
  input : P → I
  /-- Crash round (`none` = correct). -/
  crash : P → Option ℕ
  /-- The processes that still get `p`'s messages in its crashing round. -/
  reach : P → Set P

namespace Run

variable (r : Run P I)

/-- `p` has not crashed by time `m` (its local state at time `m` is not `⊥`). -/
def Alive (p : P) (m : ℕ) : Prop := ∀ c, r.crash p = some c → m < c

/-- `p` is faulty (crashes at some point) in `r`. -/
def Faulty (p : P) : Prop := r.crash p ≠ none

open Classical in
/-- The set of faulty processes. -/
noncomputable def faulty [Fintype P] : Finset P := Finset.univ.filter r.Faulty

/-- The run belongs to the model `γ_f`: at most `f` crashes, crash rounds are `≥ 1`. -/
def Admissible [Fintype P] (f : ℕ) : Prop :=
  r.faulty.card ≤ f ∧ ∀ p c, r.crash p = some c → 1 ≤ c

/-- The crash pattern as a lock-step scenario: no Byzantine parties; the message from `p` in round
`t + 1` (index `t`) is omitted iff `p` crashed in an earlier round, or crashes in this round and `q`
is not in `reach p`. -/
def toScenario (M : Type*) : Cslib.Byzantine.LockStep.Scenario P I M where
  byz := ∅
  input := r.input
  adv _ _ _ := none
  drop t p q := ∃ c, r.crash p = some c ∧ (c ≤ t ∨ (c = t + 1 ∧ q ∉ r.reach p))

variable {r}

lemma Alive.mono {p : P} {m m' : ℕ} (h : r.Alive p m) (hm : m' ≤ m) : r.Alive p m' :=
  fun c hc => lt_of_le_of_lt hm (h c hc)

lemma alive_of_not_faulty {p : P} (h : ¬ r.Faulty p) (m : ℕ) : r.Alive p m := by
  intro c hc; exact (h (by simp [Faulty, hc])).elim

@[simp] lemma mem_faulty [Fintype P] {p : P} : p ∈ r.faulty ↔ r.Faulty p := by
  simp [faulty]

lemma Admissible.alive_zero [Fintype P] {f : ℕ} (h : r.Admissible f) (p : P) : r.Alive p 0 :=
  fun c hc => h.2 p c hc

/-- In `γ_f` with `f < n` some process is correct. -/
lemma Admissible.exists_correct [Fintype P] {f : ℕ} (h : r.Admissible f)
    (hf : f < Fintype.card P) : ∃ p, ¬ r.Faulty p := by
  by_contra hc
  push Not at hc
  have : r.faulty = Finset.univ := by ext p; simp [hc p]
  have := h.1
  simp_all only [Finset.card_univ]
  omega

end Run

variable (alg : Cslib.Byzantine.LockStep.Protocol P I M O)

/-- The history (list of inboxes) of `p` after `m` rounds of the run (meaningful while `p` is
alive). -/
noncomputable def hist (r : Run P I) (m : ℕ) (p : P) : Cslib.Byzantine.LockStep.History P M :=
  Cslib.Byzantine.LockStep.hist ⊤ alg (r.toScenario M) m p

/-- The message `q` receives from `p` in round `t + 1` (sent at time `t`), if any. -/
noncomputable def msg (r : Run P I) (p q : P) (t : ℕ) : Option M :=
  Cslib.Byzantine.LockStep.deliver ⊤ alg (r.toScenario M) (hist alg r t) t p q

/-- A message is sent from `p` to `q` at time `t` (i.e. in round `t + 1`). -/
def Sent (r : Run P I) (p q : P) (t : ℕ) : Prop := msg alg r p q t ≠ none

open Classical in
/-- The local state of `p` at time `m`: its input and history, or `⊥` (`none`) once crashed. -/
noncomputable def state (r : Run P I) (p : P) (m : ℕ) :
    Option (I × Cslib.Byzantine.LockStep.History P M) :=
  if r.Alive p m then some (r.input p, hist alg r m p) else none

/-- `p` performs an action `α` (a predicate on local states) at time `m` of `r`. -/
def Performs (r : Run P I) (p : P) (m : ℕ) (α : I → Cslib.Byzantine.LockStep.History P M → Prop) :
    Prop :=
  ∃ x h, state alg r p m = some (x, h) ∧ α x h

/-- `p` decides `d` at time `m` of `r` (at the beginning of round `m + 1`; crashed processes do not
decide). -/
def DecidesAt (r : Run P I) (p : P) (m : ℕ) (d : O) : Prop :=
  Performs alg r p m (fun x h => alg.decide p x h = some d)

/-- **Knowledge** (Definition 1 of Goren–Moses): `K_p φ` holds at time `m` in `r` w.r.t. the system
`R(alg, γ_f)` iff `φ` holds in every admissible run in which `p` has the same local state at time
`m`. -/
def Knows [Fintype P] (f : ℕ) (p : P) (m : ℕ) (r : Run P I) (φ : Run P I → Prop) : Prop :=
  ∀ r' : Run P I, r'.Admissible f → state alg r' p m = state alg r p m → φ r'

/-- Message chains: `Chain alg r i m i' m'` iff `(i, m) ⇝ (i', m')`: either `i = i'` and `m ≤ m'`,
or there are messages `i = j₀ → j₁ → ⋯ → j_ℓ = i'` sent at times `m ≤ t₀ < t₁ < ⋯ < t_{ℓ-1} < m'`.
-/
inductive Chain (r : Run P I) : P → ℕ → P → ℕ → Prop
  | refl {i : P} {m m' : ℕ} : m ≤ m' → Chain r i m i m'
  | snoc {i y z : P} {m t m' : ℕ} : Chain r i m y t → Sent alg r y z t → t + 1 ≤ m' →
      Chain r i m z m'

/-- The set of messages sent in a run, as triples `(sender, receiver, sending time)`. -/
def msgs (r : Run P I) : Set (P × P × ℕ) := {e | Sent alg r e.1 e.2.1 e.2.2}

/-! ### Basic lemmas -/

variable {alg}

lemma hist_succ (r : Run P I) (t : ℕ) (q : P) :
    hist alg r (t + 1) q = hist alg r t q ++ [fun p => msg alg r p q t] := rfl

@[simp] lemma hist_zero (r : Run P I) (q : P) : hist alg r 0 q = [] := rfl

@[simp] lemma length_hist (r : Run P I) (m : ℕ) (q : P) : (hist alg r m q).length = m :=
  Cslib.Byzantine.LockStep.length_hist _ _ _ _ _

/-- Inbox lookups in a history are stable: entry `t` of `q`'s history (for `t < m`) is what `q`
received in round `t + 1`. -/
lemma hist_getElem? (r : Run P I) {t m : ℕ} (q : P) (ht : t < m) :
    (hist alg r m q)[t]? = some (fun p => msg alg r p q t) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [hist_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | rfl
    · rw [List.getElem?_append_left (by simpa using h), ih h]
    · rw [List.getElem?_append_right (by simp)]
      simp

lemma hist_getElem?_of_le (r : Run P I) {t m : ℕ} (q : P) (ht : m ≤ t) :
    (hist alg r m q)[t]? = none := by
  simp [ht]

open Classical in
lemma msg_eq (r : Run P I) (p q : P) (t : ℕ) :
    msg alg r p q t =
      if p ≠ q ∧ r.Alive p t ∧ ¬ (r.crash p = some (t + 1) ∧ q ∉ r.reach p) then
        alg.send p (r.input p) (hist alg r t p) q else none := by
  unfold msg Cslib.Byzantine.LockStep.deliver
  simp only [SimpleGraph.top_adj, Run.toScenario, Set.mem_empty_iff_false, ite_false, Run.Alive]
  by_cases h1 : p = q
  · simp [h1]
  by_cases h2 : ∃ c, r.crash p = some c ∧ (c ≤ t ∨ (c = t + 1 ∧ q ∉ r.reach p))
  · have h3 : ¬ ((∀ (c : ℕ), r.crash p = some c → t < c) ∧
        ¬(r.crash p = some (t + 1) ∧ q ∉ r.reach p)) := by
      rintro ⟨ha, hn⟩
      obtain ⟨c, hc, h | ⟨rfl, hq⟩⟩ := h2
      · exact absurd (ha c hc) (by omega)
      · exact hn ⟨hc, hq⟩
    simp only [h1, h2, h3, ne_eq, not_false_eq_true, true_and, ite_true, ite_false]
  · have h3 : (∀ (c : ℕ), r.crash p = some c → t < c) ∧
        ¬(r.crash p = some (t + 1) ∧ q ∉ r.reach p) := by
      push Not at h2
      refine ⟨fun c hc => ?_, fun hc => hc.2 ((h2 _ hc.1).2 rfl)⟩
      have := h2 c hc
      by_contra hle
      exact absurd this.1 (by omega)
    simp only [h1, h2, h3, ne_eq, not_false_eq_true, true_and, ite_true, ite_false, and_true]
    exact (ite_eq_left h3.1).symm

lemma sent_iff (r : Run P I) (p q : P) (t : ℕ) :
    Sent alg r p q t ↔ p ≠ q ∧ r.Alive p t ∧ ¬ (r.crash p = some (t + 1) ∧ q ∉ r.reach p) ∧
      alg.send p (r.input p) (hist alg r t p) q ≠ none := by
  unfold Sent
  rw [msg_eq]
  split_ifs with h
  · tauto
  · simp only [ne_eq, not_true_eq_false, false_iff]
    tauto

lemma Sent.ne {r : Run P I} {p q : P} {t : ℕ} (h : Sent alg r p q t) : p ≠ q :=
  ((sent_iff r p q t).1 h).1

lemma Sent.alive {r : Run P I} {p q : P} {t : ℕ} (h : Sent alg r p q t) : r.Alive p t :=
  ((sent_iff r p q t).1 h).2.1

lemma state_eq_none {r : Run P I} {p : P} {m : ℕ} : state alg r p m = none ↔ ¬ r.Alive p m := by
  unfold state; split_ifs with h <;> simp [h]

lemma state_of_alive {r : Run P I} {p : P} {m : ℕ} (h : r.Alive p m) :
    state alg r p m = some (r.input p, hist alg r m p) := by
  unfold state; rw [ite_eq_left h]

lemma decidesAt_iff {r : Run P I} {p : P} {m : ℕ} {d : O} :
    DecidesAt alg r p m d ↔ r.Alive p m ∧ alg.decide p (r.input p) (hist alg r m p) = some d := by
  unfold DecidesAt Performs state
  split_ifs with h <;> simp [h]

/-- Deterministic protocols: a process performs the same actions in runs it cannot distinguish. -/
lemma Performs.of_state_eq {r r' : Run P I} {p : P} {m : ℕ} {α}
    (h : Performs alg r p m α) (he : state alg r' p m = state alg r p m) :
    Performs alg r' p m α := by
  obtain ⟨x, hh, hs, hα⟩ := h
  exact ⟨x, hh, he.trans hs, hα⟩

/-- **Knowledge property**: what is known is true. -/
lemma Knows.holds [Fintype P] {f : ℕ} {p : P} {m : ℕ} {r : Run P I} {φ : Run P I → Prop}
    (h : Knows alg f p m r φ) (hr : r.Admissible f) : φ r :=
  h r hr rfl

lemma Knows.mono [Fintype P] {f : ℕ} {p : P} {m : ℕ} {r : Run P I} {φ ψ : Run P I → Prop}
    (h : Knows alg f p m r φ) (hφψ : ∀ r', r'.Admissible f → φ r' → ψ r') :
    Knows alg f p m r ψ :=
  fun r' hr' he => hφψ r' hr' (h r' hr' he)

/-- **Knowledge of preconditions** (KoP, Theorem 1 of Goren–Moses, after Moses 2015): if `φ` is a
necessary condition for an action `α` of `p` in `R(alg, γ_f)`, then so is `K_p φ`. -/
theorem kop [Fintype P] {f : ℕ} {p : P} {α : I → Cslib.Byzantine.LockStep.History P M → Prop}
    {φ : Run P I → Prop}
    (hnec : ∀ r : Run P I, r.Admissible f → ∀ m, Performs alg r p m α → φ r)
    {r : Run P I} {m : ℕ} (hα : Performs alg r p m α) : Knows alg f p m r φ :=
  fun r' hr' he => hnec r' hr' m (hα.of_state_eq he)

/-- The delivery condition of the crash pattern: a message from `p` to `q` in round `t + 1` is
delivered iff `p` is alive at time `t` and, if `p` crashes in round `t + 1`, `q ∈ reach p`. -/
def Run.Deliv (r : Run P I) (p q : P) (t : ℕ) : Prop :=
  r.Alive p t ∧ ¬ (r.crash p = some (t + 1) ∧ q ∉ r.reach p)

open Classical in
lemma msg_eq_deliv (r : Run P I) (p q : P) (t : ℕ) :
    msg alg r p q t =
      if p ≠ q ∧ r.Deliv p q t then alg.send p (r.input p) (hist alg r t p) q else none := by
  rw [msg_eq]; split_ifs <;> simp_all [Run.Deliv]

lemma sent_iff_deliv (r : Run P I) (p q : P) (t : ℕ) :
    Sent alg r p q t ↔ p ≠ q ∧ r.Deliv p q t ∧
      alg.send p (r.input p) (hist alg r t p) q ≠ none := by
  rw [sent_iff]; simp only [Run.Deliv, and_assoc]

lemma Sent.deliv {r : Run P I} {p q : P} {t : ℕ} (h : Sent alg r p q t) : r.Deliv p q t :=
  ((sent_iff_deliv r p q t).1 h).2.1

lemma Sent.send_ne_none {r : Run P I} {p q : P} {t : ℕ} (h : Sent alg r p q t) :
    alg.send p (r.input p) (hist alg r t p) q ≠ none :=
  ((sent_iff_deliv r p q t).1 h).2.2

/-- A message sent by a process that crashes in round `c` is sent in a round `≤ c`, and in round `c`
only to `reach p`. -/
lemma Sent.le_crash {r : Run P I} {p q : P} {t c : ℕ} (h : Sent alg r p q t)
    (hc : r.crash p = some c) : t + 1 ≤ c ∧ (t + 1 = c → q ∈ r.reach p) := by
  obtain ⟨ha, hn⟩ := h.deliv
  refine ⟨ha c hc, fun he => ?_⟩
  by_contra hq
  exact hn ⟨he ▸ hc, hq⟩

lemma msg_congr {r r' : Run P I} {p q : P} {t : ℕ} (hin : r.input p = r'.input p)
    (hh : r.Alive p t → hist alg r t p = hist alg r' t p) (hd : r.Deliv p q t ↔ r'.Deliv p q t) :
    msg alg r p q t = msg alg r' p q t := by
  rw [msg_eq_deliv, msg_eq_deliv]
  by_cases h : p ≠ q ∧ r.Deliv p q t
  · rw [ite_eq_left h, ite_eq_left ⟨h.1, hd.1 h.2⟩, hin, hh h.2.1]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.1, hd.2 h'.2⟩)]

/-- Two runs with the same inputs and the same delivery pattern in the first `T` rounds have the
same histories up to time `T`. -/
lemma hist_congr {r r' : Run P I} {T : ℕ} (hin : ∀ p, r.input p = r'.input p)
    (hd : ∀ t < T, ∀ p q, r.Deliv p q t ↔ r'.Deliv p q t) :
    ∀ t ≤ T, ∀ p, hist alg r t p = hist alg r' t p := by
  intro t
  induction t with
  | zero => intros; rfl
  | succ t ih =>
    intro ht p
    rw [hist_succ, hist_succ, ih (by omega)]
    congr 2
    funext y
    exact msg_congr (hin y) (fun _ => ih (by omega) y) (hd t (by omega) y p)

/-- The message received from `p` in round `t + 1`, read off a history (`none` if no message or if
the history is shorter). Protocols use this to inspect their history. -/
def rcv (h : Cslib.Byzantine.LockStep.History P M) (t : ℕ) (p : P) : Option M :=
  (h[t]?).bind (fun inbox => inbox p)

lemma rcv_hist (r : Run P I) {t m : ℕ} (q p : P) (ht : t < m) :
    rcv (hist alg r m q) t p = msg alg r p q t := by
  simp [rcv, hist_getElem? r q ht]

lemma Run.deliv_of_not_faulty {r : Run P I} {p : P} (h : ¬ r.Faulty p) (q : P) (t : ℕ) :
    r.Deliv p q t :=
  ⟨Run.alive_of_not_faulty h t, fun hc => h (by simp [Run.Faulty, hc.1])⟩

lemma sent_of_deliv {r : Run P I} {p q : P} {t : ℕ} (hpq : p ≠ q) (hd : r.Deliv p q t)
    (hs : alg.send p (r.input p) (hist alg r t p) q ≠ none) : Sent alg r p q t :=
  (sent_iff_deliv r p q t).2 ⟨hpq, hd, hs⟩

/-! ### Message chains -/

namespace Chain

variable {r : Run P I}

lemma trans_le {i z : P} {m t t' : ℕ} (h : Chain alg r i m z t) (ht : t ≤ t') :
    Chain alg r i m z t' := by
  induction h with
  | refl h => exact refl (by omega)
  | snoc _ hs hle _ => exact snoc ‹_› hs (by omega)

lemma le {i z : P} {m t : ℕ} (h : Chain alg r i m z t) : m ≤ t := by
  induction h with
  | refl h => exact h
  | snoc _ _ hle ih => omega

/-- A chain to another process takes at least one round. -/
lemma lt_of_ne {i z : P} {m t : ℕ} (h : Chain alg r i m z t) (hne : z ≠ i) : m < t := by
  induction h with
  | refl h => exact absurd rfl hne
  | snoc hc _ hle _ => have := hc.le; omega

lemma step {i y z : P} {m t : ℕ} (h : Chain alg r i m y t) (hs : Sent alg r y z t) :
    Chain alg r i m z (t + 1) := snoc h hs le_rfl

/-- Prepending a message. -/
lemma cons {i y z : P} {m t t' : ℕ} (hs : Sent alg r i y t) (hmt : m ≤ t)
    (h : Chain alg r y (t + 1) z t') : Chain alg r i m z t' := by
  generalize hs1 : t + 1 = s at h
  induction h with
  | refl h => subst hs1; exact snoc (refl hmt) hs h
  | snoc _ hs' hle ih => exact snoc (ih hs1) hs' hle

lemma trans {i y z : P} {m t t' : ℕ} (h₁ : Chain alg r i m y t) (h₂ : Chain alg r y t z t') :
    Chain alg r i m z t' := by
  induction h₂ with
  | refl h => exact h₁.trans_le h
  | snoc _ hs hle ih => exact snoc (ih h₁) hs hle

/-- The first message of a chain to another process is sent by its origin. -/
lemma exists_first {i z : P} {m t : ℕ} (h : Chain alg r i m z t) (hne : z ≠ i) :
    ∃ y t', Sent alg r i y t' ∧ m ≤ t' ∧ t' < t := by
  induction h with
  | refl h => exact absurd rfl hne
  | snoc hc hs hle ih =>
    rename_i w z' m' t₀ m''
    by_cases hy : w = i
    · subst hy; exact ⟨z', t₀, hs, hc.le, by omega⟩
    · obtain ⟨y', t', h1, h2, h3⟩ := ih hy
      exact ⟨y', t', h1, h2, by omega⟩

/-- The last message of a chain to another process. -/
lemma exists_last {i z : P} {m t : ℕ} (h : Chain alg r i m z t) (hne : z ≠ i) :
    ∃ y t', Chain alg r i m y t' ∧ Sent alg r y z t' ∧ t' < t := by
  cases h with
  | refl h => exact absurd rfl hne
  | snoc hc hs hle => exact ⟨_, _, hc, hs, by omega⟩

lemma eq_of_le {i z : P} {m t : ℕ} (h : Chain alg r i m z t) (ht : t ≤ m) : z = i := by
  by_contra hne
  have := h.lt_of_ne hne
  omega

end Chain

end Cslib.SyncCrash
