/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.MessagePassing.Spec
public import Mathlib.Data.Fintype.EquivFin

/-! # Existence of valid runs

Correctness of a protocol is stated as `Protocol.Satisfies`: every valid run satisfies the
specification. This file shows that such statements are not vacuous: every protocol has valid
runs, for every set of at most `t` faulty processes, every GST, every delay bound `δ > 0` and
every environment, i.e. every choice of the requests each process handles at each time.

The run constructed is *synchronous*: local clocks show real time, every message sent at time
`τ` is delivered at time `τ + 1`, and faulty processes follow the protocol too. At time `τ`,
process `p` handles the requests of the environment, then the messages sent to it at time
`τ - 1` (by all processes, in the order of `Finset.univ.toList`), then its timers expiring at
time `τ`. Since the inputs at time `τ` depend on the outputs at earlier times, which depend on
the inputs at earlier times, the inputs are defined by recursion on time.

## Main definitions

* `Protocol.syncRun A F gst env`: the synchronous run with faulty processes `F`, GST `gst` and
  requests `env p τ`.

## Main statements

* `Protocol.syncRun_valid`: the synchronous run is valid.
* `Protocol.exists_valid_run`: valid runs exist for every protocol and every environment.
* `Protocol.Satisfies.exists_run_of_env`: non-vacuity of specifications whose environment
  assumptions only constrain the faulty processes, the GST and the requests (prescribed with
  `History.HasRequests`).
* `History.HasRequests.countP_events`, `History.HasRequests.atMostOnce`: counting the requests of
  a history with prescribed requests.
-/

@[expose] public section

namespace Cslib.Distributed

variable {P : Type*} {I : Interface}

/-! ### The synchronous run -/

namespace Protocol

variable (A : Protocol P I)

/-- In the synchronous run, the input with which process `q` receives an output `o` of process
`p`: `recv p m` if `o` sends `m` to `q`. -/
def syncDeliver [DecidableEq P] (p q : P) : A.Out → Option A.In
  | .send q' m => if q' = q then some (.recv p m) else none
  | _ => none

/-- In the synchronous run (where local clocks show real time), the timeout caused at time `τ` by
an output `o` produced at time `τ'`: `timeout k` if `o` sets the timer `k` and it expires at
`τ`, i.e. `τ` is the first time after `τ'` not before the deadline. -/
def syncExpire (τ' τ : ℕ) : A.Out → Option A.In
  | .setTimer k T => if max (τ' + 1) T = τ then some (.timeout k) else none
  | _ => none

/-- The run with inputs `input` in which local clocks show real time (and nobody is faulty). -/
def clockRun (input : P → ℕ → List A.In) : Run A where
  faulty := ∅
  gst := 0
  clock _ τ := τ
  input := input

section Sync

variable [Fintype P] [DecidableEq P]

/-- The messages delivered to `p` at time `τ` in the synchronous run, given the outputs `out`:
those sent to `p` at time `τ - 1`, by all processes in the order of `Finset.univ.toList`. -/
noncomputable def syncDeliveries (out : P → ℕ → List A.Out) (p : P) : ℕ → List A.In
  | 0 => []
  | τ + 1 =>
    (Finset.univ : Finset P).toList.flatMap fun q => (out q τ).filterMap (A.syncDeliver q p)

/-- The inputs of `p` at time `τ` in the synchronous run, given the requests `env` and the
outputs `out` at earlier times: the requests `env p τ`, then the messages sent to `p` at time
`τ - 1`, then the timers of `p` expiring at time `τ`. -/
noncomputable def syncInput (env : P → ℕ → List I.Req) (out : P → ℕ → List A.Out) (p : P)
    (τ : ℕ) : List A.In :=
  (env p τ).map .req ++ A.syncDeliveries out p τ ++
    (List.range τ).flatMap fun τ' => (out p τ').filterMap (A.syncExpire τ' τ)

/-- The inputs of the synchronous run at the times before `n` (and `[]` at later times). -/
noncomputable def syncInputUpTo (env : P → ℕ → List I.Req) : ℕ → P → ℕ → List A.In
  | 0 => fun _ _ => []
  | n + 1 => fun p τ =>
    if τ = n then A.syncInput env (A.clockRun (syncInputUpTo env n)).output p n
    else syncInputUpTo env n p τ

/-- The synchronous run of `A` with faulty processes `F`, GST `gst` and requests `env`: local
clocks show real time, every message sent at time `τ` is delivered at time `τ + 1`, and all
processes (including the faulty ones) follow the protocol. At time `τ`, process `p` handles the
requests `env p τ`, then the messages sent to it at time `τ - 1`, then its timers expiring at
time `τ` (`Protocol.syncInput`). -/
noncomputable def syncRun (F : Finset P) (gst : ℕ) (env : P → ℕ → List I.Req) : Run A where
  faulty := F
  gst := gst
  clock _ τ := τ
  input p τ := A.syncInputUpTo env (τ + 1) p τ

end Sync

variable {A}

theorem syncDeliver_eq_some [DecidableEq P] {p q : P} {o : A.Out} {x : A.In} :
    A.syncDeliver p q o = some x ↔ ∃ m, o = .send q m ∧ x = .recv p m := by
  cases o with
  | send q' m =>
    by_cases h : q' = q
    · subst h; simp [syncDeliver, eq_comm]
    · simp [syncDeliver, h]
  | ind => simp [syncDeliver]
  | setTimer => simp [syncDeliver]

theorem syncExpire_eq_some {τ' τ : ℕ} {o : A.Out} {x : A.In} :
    A.syncExpire τ' τ o = some x ↔
      ∃ k T, o = .setTimer k T ∧ max (τ' + 1) T = τ ∧ x = .timeout k := by
  cases o with
  | send => simp [syncExpire]
  | ind => simp [syncExpire]
  | setTimer k T =>
    by_cases h : max (τ' + 1) T = τ
    · simp [syncExpire, h, eq_comm]
    · simp [syncExpire, h]

section Sync

variable [Fintype P] [DecidableEq P]

theorem mem_syncDeliveries {out : P → ℕ → List A.Out} {p : P} {τ : ℕ} {x : A.In} :
    x ∈ A.syncDeliveries out p τ ↔
      ∃ q m τ', τ = τ' + 1 ∧ .send p m ∈ out q τ' ∧ x = .recv q m := by
  cases τ with
  | zero => simp [syncDeliveries]
  | succ τ =>
    simp only [syncDeliveries, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and,
      List.mem_filterMap, syncDeliver_eq_some, Nat.add_right_cancel_iff, exists_eq_left']
    constructor
    · rintro ⟨q, o, ho, m, rfl, rfl⟩
      exact ⟨q, m, ho, rfl⟩
    · rintro ⟨q, m, ho, rfl⟩
      exact ⟨q, _, ho, m, rfl, rfl⟩

theorem mem_syncInput {env : P → ℕ → List I.Req} {out : P → ℕ → List A.Out} {p : P} {τ : ℕ}
    {x : A.In} :
    x ∈ A.syncInput env out p τ ↔ (∃ r ∈ env p τ, x = .req r) ∨
      (∃ q m τ', τ = τ' + 1 ∧ .send p m ∈ out q τ' ∧ x = .recv q m) ∨
      (∃ k T τ', τ' < τ ∧ .setTimer k T ∈ out p τ' ∧ max (τ' + 1) T = τ ∧ x = .timeout k) := by
  simp only [syncInput, List.mem_append, List.mem_map, mem_syncDeliveries, List.mem_flatMap,
    List.mem_range, List.mem_filterMap, syncExpire_eq_some]
  constructor
  · rintro ((⟨r, hr, rfl⟩ | h) | ⟨τ', hτ', o, ho, k, T, rfl, hT, rfl⟩)
    · exact .inl ⟨r, hr, rfl⟩
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨k, T, τ', hτ', ho, hT, rfl⟩)
  · rintro (⟨r, hr, rfl⟩ | h | ⟨k, T, τ', hτ', ho, hT, rfl⟩)
    · exact .inl (.inl ⟨r, hr, rfl⟩)
    · exact .inl (.inr h)
    · exact .inr ⟨τ', hτ', _, ho, k, T, rfl, hT, rfl⟩

/-- The requests among the inputs of the synchronous run are those of the environment. -/
theorem filterMap_req?_syncInput (env : P → ℕ → List I.Req) (out : P → ℕ → List A.Out) (p : P)
    (τ : ℕ) : (A.syncInput env out p τ).filterMap Input.req? = env p τ := by
  have hnet : ∀ x ∈ A.syncDeliveries out p τ ++
      (List.range τ).flatMap fun τ' => (out p τ').filterMap (A.syncExpire τ' τ),
      x.req? = none := by
    simp only [List.mem_append, mem_syncDeliveries, List.mem_flatMap, List.mem_filterMap,
      syncExpire_eq_some]
    rintro x (⟨q, m, τ', -, -, rfl⟩ | ⟨τ', -, o, -, k, T, -, -, rfl⟩) <;> rfl
  rw [syncInput, List.append_assoc, List.filterMap_append, List.filterMap_eq_nil_iff.2 hnet,
    List.append_nil, List.filterMap_map]
  exact List.filterMap_some

/-- The inputs of the synchronous run at time `τ` depend only on the outputs before `τ`. -/
theorem syncInput_congr {env : P → ℕ → List I.Req} {out out' : P → ℕ → List A.Out} {p : P}
    {τ : ℕ} (h : ∀ q, ∀ τ' < τ, out q τ' = out' q τ') :
    A.syncInput env out p τ = A.syncInput env out' p τ := by
  have hdel : A.syncDeliveries out p τ = A.syncDeliveries out' p τ := by
    cases τ with
    | zero => rfl
    | succ τ => simp only [syncDeliveries, h _ τ (by omega)]
  rw [syncInput, syncInput, hdel]
  congr 1
  exact List.flatMap_congr fun τ' hτ' => by rw [h p τ' (List.mem_range.1 hτ')]

theorem syncInputUpTo_eq {env : P → ℕ → List I.Req} {n τ : ℕ} (h : τ < n) (p : P) :
    A.syncInputUpTo env n p τ = A.syncInputUpTo env (τ + 1) p τ := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hτ : τ = n
    · subst hτ; rfl
    · simp only [syncInputUpTo, hτ, ↓reduceIte, ih (by omega : τ < n)]

@[simp]
theorem syncRun_faulty (F : Finset P) (gst : ℕ) (env : P → ℕ → List I.Req) :
    (A.syncRun F gst env).faulty = F := rfl

@[simp]
theorem syncRun_gst (F : Finset P) (gst : ℕ) (env : P → ℕ → List I.Req) :
    (A.syncRun F gst env).gst = gst := rfl

@[simp]
theorem syncRun_clock (F : Finset P) (gst : ℕ) (env : P → ℕ → List I.Req) (p : P) (τ : ℕ) :
    (A.syncRun F gst env).clock p τ = τ := rfl

/-- The inputs of the synchronous run are computed from its outputs at earlier times by
`Protocol.syncInput`. -/
theorem syncRun_input (F : Finset P) (gst : ℕ) (env : P → ℕ → List I.Req) (p : P) (τ : ℕ) :
    (A.syncRun F gst env).input p τ =
      A.syncInput env (A.syncRun F gst env).output p τ := by
  change A.syncInputUpTo env (τ + 1) p τ = _
  simp only [syncInputUpTo, ↓reduceIte]
  refine syncInput_congr fun q τ' hτ' => Run.output_congr (fun _ _ => rfl) fun τ'' hτ'' => ?_
  exact syncInputUpTo_eq (by omega) q

/-- In the synchronous run, process `p` handles exactly the requests `env p τ` at time `τ`, in
this order. -/
theorem filterMap_req?_syncRun_input (F : Finset P) (gst : ℕ) (env : P → ℕ → List I.Req)
    (p : P) (τ : ℕ) : ((A.syncRun F gst env).input p τ).filterMap Input.req? = env p τ := by
  rw [syncRun_input, filterMap_req?_syncInput]

theorem syncRun_hasRequests (F : Finset P) (gst : ℕ) (env : P → ℕ → List I.Req) :
    (A.syncRun F gst env).history.HasRequests env := fun p τ => by
  simp [Run.filterMap_req?_trace, filterMap_req?_syncRun_input]

/-- With clocks showing real time, a timer set at `τ'` with deadline `T` expires exactly at
`max (τ' + 1) T`. -/
theorem syncRun_expires_iff {F : Finset P} {gst : ℕ} {env : P → ℕ → List I.Req} {p : P}
    {τ' T τ : ℕ} : (A.syncRun F gst env).Expires p τ' T τ ↔ max (τ' + 1) T = τ := by
  simp only [Run.Expires, syncRun_clock]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    have := h₃ (max (τ' + 1) T)
    omega
  · rintro rfl
    exact ⟨by omega, by omega, fun τ'' h₁ h₂ => by omega⟩

/-- The synchronous run is valid for every delay bound `δ > 0` if at most `t` processes are
faulty. -/
theorem syncRun_valid {t δ : ℕ} {F : Finset P} (hF : F.card ≤ t) (hδ : 0 < δ) (gst : ℕ)
    (env : P → ℕ → List I.Req) : (A.syncRun F gst env).Valid t δ where
  card_faulty_le := hF
  clock_mono _ _ _ h := h
  clock_succ _ := rfl
  authentic {p q m τ} _ _ h := by
    rw [syncRun_input, mem_syncInput] at h
    rcases h with ⟨r, -, h⟩ | ⟨q', m', τ', rfl, h, he⟩ | ⟨k, T, τ', -, -, -, h⟩
    · cases h
    · cases he
      exact ⟨τ', by omega, h, by simp; omega⟩
    · cases h
  reliable {p q m τ} _ _ h := by
    refine ⟨τ + 1, by omega, by simp; omega, ?_⟩
    rw [syncRun_input, mem_syncInput]
    exact .inr (.inl ⟨p, m, τ, rfl, h, rfl⟩)
  timer {p k τ} _ := by
    rw [syncRun_input, mem_syncInput]
    simp only [syncRun_expires_iff]
    constructor
    · rintro (⟨r, -, h⟩ | ⟨q, m, τ', -, -, h⟩ | ⟨k', T, τ', -, h, hT, he⟩)
      · cases h
      · cases h
      · cases he
        exact ⟨τ', T, h, hT⟩
    · rintro ⟨τ', T, h, hT⟩
      exact .inr (.inr ⟨k, T, τ', by omega, h, hT, rfl⟩)

end Sync

/-! ### Non-vacuity -/

/-- **Valid runs exist** for every protocol, every set `F` of at most `t` faulty processes, every
GST, every delay bound `δ > 0` and every environment: the requests that each process `p` handles
at each time `τ` can be prescribed to be `env p τ` (in this order). -/
theorem exists_valid_run (A : Protocol P I) [Finite P] {t : ℕ} (F : Finset P) (hF : F.card ≤ t)
    (gst δ : ℕ) (hδ : 0 < δ) (env : P → ℕ → List I.Req) :
    ∃ ρ : Run A, ρ.Valid t δ ∧ ρ.faulty = F ∧ ρ.gst = gst ∧
      ∀ p τ, (ρ.input p τ).filterMap Input.req? = env p τ := by
  classical
  have := Fintype.ofFinite P
  exact ⟨A.syncRun F gst env, syncRun_valid hF hδ gst env, rfl, rfl,
    filterMap_req?_syncRun_input F gst env⟩

/-- A protocol satisfying a specification has a valid run with any prescribed faulty processes,
GST and requests, and the history of this run satisfies the specification. -/
theorem Satisfies.exists_run {A : Protocol P I} [Finite P] {t δ : ℕ} {S : Spec P I}
    (hA : A.Satisfies t δ S) (hδ : 0 < δ) {F : Finset P} (hF : F.card ≤ t) (gst : ℕ)
    (env : P → ℕ → List I.Req) :
    ∃ ρ : Run A, ρ.Valid t δ ∧ ρ.faulty = F ∧ ρ.gst = gst ∧ ρ.history.HasRequests env ∧
      S ρ.history := by
  classical
  have := Fintype.ofFinite P
  exact ⟨A.syncRun F gst env, syncRun_valid hF hδ gst env, rfl, rfl, syncRun_hasRequests F gst env,
    hA _ (syncRun_valid hF hδ gst env)⟩

/-- **Non-vacuity of specifications.** Let `Env` be a predicate on histories (typically the
environment assumptions of a specification `S = fun H => Env H → G H`) that holds for every
history with faulty processes `F` (at most `t` of them), GST `gst` and requests `env`. Then a
protocol satisfying `S` has a valid run whose history satisfies both `Env` and `S`. -/
theorem Satisfies.exists_run_of_env {A : Protocol P I} [Finite P] {t δ : ℕ} {S Env : Spec P I}
    (hA : A.Satisfies t δ S) (hδ : 0 < δ) {F : Finset P} (hF : F.card ≤ t) {gst : ℕ}
    {env : P → ℕ → List I.Req}
    (hEnv : ∀ H : History P I, H.faulty = F → H.gst = gst → H.HasRequests env → Env H) :
    ∃ ρ : Run A, ρ.Valid t δ ∧ Env ρ.history ∧ S ρ.history := by
  obtain ⟨ρ, hρ, hfaulty, hgst, hreq, hS⟩ := hA.exists_run hδ hF gst env
  exact ⟨ρ, hρ, hEnv _ hfaulty hgst hreq, hS⟩

end Protocol

/-! ### Requests of histories -/

namespace History.HasRequests

variable {H : History P I} {env : P → ℕ → List I.Req}

/-- In a history with prescribed requests, counting the events of a kind that contains no
indication is counting the prescribed requests of that kind. -/
theorem countP_events (h : H.HasRequests env) {b : Event I → Bool} (hb : ∀ i, b (.ind i) = false)
    (p : P) (T : ℕ) :
    (H.events p T).countP b = ((List.range T).flatMap (env p)).countP fun r => b (.req r) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [History.events_succ, List.countP_append, ih, List.range_succ, List.flatMap_append,
      List.countP_append, Event.countP_eq_countP_filterMap_req? hb, h p T]
    simp

/-- In a history with prescribed requests, a kind of event that contains no indication occurs at
most once if it is prescribed at most once. -/
theorem atMostOnce (h : H.HasRequests env) {p : P} {b : Event I → Bool}
    (hb : ∀ i, b (.ind i) = false)
    (henv : ∀ T, ((List.range T).flatMap (env p)).countP (fun r => b (.req r)) ≤ 1) :
    H.AtMostOnce p b :=
  fun T => (h.countP_events hb p T).trans_le (henv T)

end History.HasRequests

end Cslib.Distributed
