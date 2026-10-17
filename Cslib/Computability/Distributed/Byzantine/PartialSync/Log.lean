/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Auth

/-!
# Message logs of protocol implementations

Protocol implementations in the partially synchronous model (`Cslib.Byzantine.PartialSync`)
usually keep, in their local state, the list of all messages received so far, tagged with their
senders (a *message log*); their handlers then only inspect the log. `A.Logs log` says that
`log : S → List (P × M)` is such a log: it is empty initially, and every step appends exactly the
messages of the inbox. The basic facts about logs in runs follow once and for all:

* `Algorithm.Logs.mem_log_iff`: `(q, m)` is in `p`'s log at time `τ` iff `m` was delivered from
  `q` to `p` before `τ`; `Algorithm.Logs.prefix_log`, `Algorithm.Logs.mem_log_of_le`: logs grow.
* `Algorithm.Logs.exists_mem_send_of_mem_log` (authenticity): a logged message from a correct
  sender was sent by it earlier, to this receiver.
* `Algorithm.Logs.mem_log_of_valid` (delivery): in a valid run, a message between correct
  processes sent at `σ` is logged by time `max σ gst + δ + 1`.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

variable {P M S VI VO : Type*} [DecidableEq P]

/-- `log : S → List (P × M)` is a *message log* of `A`: it is empty initially, and every step
appends exactly the delivered messages, tagged with their senders. -/
structure Algorithm.Logs (A : Algorithm P M S VI VO) (log : S → List (P × M)) : Prop where
  /-- The log is initially empty. -/
  log_init : ∀ p v, log (A.init p v) = []
  /-- A step appends the messages of the inbox to the log. -/
  log_step : ∀ p s ib, ∃ l, log (A.step p s ib) = log s ++ l ∧ ∀ q m, (q, m) ∈ l ↔ m ∈ ib q

namespace Algorithm.Logs

variable {A : Algorithm P M S VI VO} {log : S → List (P × M)} (hA : A.Logs log) (R : Run P M VI)
include hA

/-- One step of a run appends the inbox to the log. -/
theorem mem_log_st_succ_iff (τ : ℕ) (p q : P) (m : M) :
    (q, m) ∈ log (R.st A (τ + 1) p) ↔ (q, m) ∈ log (R.st A τ p) ∨ m ∈ R.inbox A p τ q := by
  obtain ⟨l, hl, hm⟩ := hA.log_step p (R.st A τ p) (R.inbox A p τ)
  rw [Run.st_succ, hl, List.mem_append, hm]

/-- Logs grow: an earlier log is a prefix of a later one. -/
theorem prefix_log {σ τ : ℕ} (h : σ ≤ τ) (p : P) : log (R.st A σ p) <+: log (R.st A τ p) := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    obtain ⟨l, hl, -⟩ := hA.log_step p (R.st A _ p) (R.inbox A p _)
    rw [Run.st_succ, hl]
    exact ih.trans (List.prefix_append _ _)

/-- Logged messages stay logged. -/
theorem mem_log_of_le {σ τ : ℕ} (h : σ ≤ τ) {p : P} {qm : P × M} (hm : qm ∈ log (R.st A σ p)) :
    qm ∈ log (R.st A τ p) :=
  (hA.prefix_log R h p).subset hm

/-- `(q, m)` is in `p`'s log at time `τ` iff `m` was delivered from `q` to `p` before `τ`. -/
theorem mem_log_iff (τ : ℕ) (p q : P) (m : M) :
    (q, m) ∈ log (R.st A τ p) ↔ ∃ ρ < τ, m ∈ R.inbox A p ρ q := by
  induction τ with
  | zero => simp [hA.log_init]
  | succ τ ih =>
    rw [hA.mem_log_st_succ_iff R, ih]
    constructor
    · rintro (⟨ρ, hρ, h⟩ | h)
      · exact ⟨ρ, by omega, h⟩
      · exact ⟨τ, by omega, h⟩
    · rintro ⟨ρ, hρ, h⟩
      rcases Nat.lt_or_ge ρ τ with h' | h'
      · exact Or.inl ⟨ρ, h', h⟩
      · obtain rfl : ρ = τ := by omega
        exact Or.inr h

/-- **Authenticity.** A logged message from a correct sender `q` was sent by `q` to this receiver
at an earlier time. -/
theorem exists_mem_send_of_mem_log {τ : ℕ} {p q : P} {m : M} (hq : q ∉ R.faulty)
    (h : (q, m) ∈ log (R.st A τ p)) : ∃ σ < τ, m ∈ A.send q (R.st A σ q) p := by
  obtain ⟨ρ, hρ, hin⟩ := (hA.mem_log_iff R τ p q m).1 h
  obtain ⟨σ, hσ, -, hm⟩ := Run.mem_inbox.1 hin
  exact ⟨σ, by omega, Run.out_of_correct A R hq σ p ▸ hm⟩

/-- **Delivery.** In a valid run, a message sent at `σ` between correct processes is in the
receiver's log from time `max σ gst + δ + 1` on. -/
theorem mem_log_of_valid {t δ : ℕ} (hR : R.Valid t δ) {p q : P} (hq : q ∉ R.faulty)
    (hp : p ∉ R.faulty) {σ : ℕ} {m : M} (hm : m ∈ A.send q (R.st A σ q) p) {τ : ℕ}
    (hτ : max σ R.gst + δ < τ) : (q, m) ∈ log (R.st A τ p) := by
  have h1 := hR.dl_ge q σ p hq hp
  have h2 := hR.dl_le q σ p hq hp
  refine (hA.mem_log_iff R τ p q m).2 ⟨R.dl q σ p, by omega, Run.mem_inbox.2 ⟨σ, h1, rfl, ?_⟩⟩
  rwa [Run.out_of_correct A R hq]

end Algorithm.Logs

end Cslib.Byzantine.PartialSync
