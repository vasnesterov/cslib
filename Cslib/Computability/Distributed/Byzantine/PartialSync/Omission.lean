/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.QuietRuns
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod

/-!
# Synchronous executions with omission failures

A lock-step synchronous execution in which some batches of messages are *omitted* (not
delivered). In contrast to Byzantine processes, omission-faulty processes run the algorithm
(on their possibly incomplete inboxes), so one can reason about their states and decisions.

* `OmExec P VI`: inputs `inp` and a delivery predicate `ok τ q p` (is the batch sent by `q` to
  `p` at time `τ` delivered?). States `OmExec.st A E τ p` are computed for **all** processes by
  recursion on time; they do not depend on who is "faulty".
* `E.Admits A F`: every omitted non-empty batch has an endpoint in `F` (and is not a
  self-message), i.e. `F` is a legal set of omission-faulty processes for `E`. Since states do
  not depend on `F`, changing `F` (e.g. "swapping receive omissions for send omissions",
  `Admits.swap`) keeps the execution indistinguishable for *every* process.
* `OmSolves t A val`: termination, agreement and validity for every `E` and admissible `F` with
  `|F| ≤ t`.
* `E.toRun A F`: the Byzantine run (`gst = 0`, zero delays) in which the processes of `F` send
  exactly what they send in `E` (minus omitted batches). Its correct processes have the states of
  `E` (`toRun_st`), it is valid (`toRun_valid`), respects unforgeability for unforging algorithms
  (`toRun_authValid`), and has the same message count (`toRun_msgsUpTo`). Hence every synchronous
  Byzantine solution is an omission solution (`SolvesConsensusAuthSync.omSolves`), and lower
  bounds proved for omission executions transfer to the Byzantine model.
* `OmExec.ff x`: the fault-free execution with inputs `x` (every batch is delivered);
  `OmExec.solo x B`: every process of `B` is *isolated*: it receives only its own messages
  (admissible with faulty set `B`, `OmExec.solo_admits`). An isolated process behaves as in any
  other execution in which it is isolated with the same input (`OmExec.solo_st`). These are the
  two executions used by message lower bounds.
* `Run.st_eq_ff`: a fault-free run with zero delays has the states of the fault-free omission
  execution; in particular the quiet fault-free run `Run.quiet ∅ x` decides as `OmExec.ff x`
  (`Run.quiet_empty_decides_iff`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P]

/-- A synchronous execution with omissions: inputs and delivered batches. -/
structure OmExec (P VI : Type*) where
  /-- Proposals of all processes. -/
  inp : P → VI
  /-- `ok τ q p`: the batch sent by `q` to `p` at time `τ` is delivered (at time `τ`). -/
  ok : ℕ → P → P → Bool

namespace OmExec

variable (A : Algorithm P M S VI VO) (E : OmExec P VI)

/-- States of all processes (for faulty ones too: omission-faulty processes run the algorithm). -/
def st : ℕ → P → S
  | 0, p => A.init p (E.inp p)
  | τ + 1, p => A.step p (st τ p) (fun q => if E.ok τ q p then A.send q (st τ q) p else [])

/-- Messages received by `p` at time `τ` from `q`. -/
def inbox (τ : ℕ) (p q : P) : List M := if E.ok τ q p then A.send q (E.st A τ q) p else []

omit [DecidableEq P] [Fintype P] in
@[simp] theorem st_zero (p : P) : E.st A 0 p = A.init p (E.inp p) := rfl

omit [DecidableEq P] [Fintype P] in
theorem st_succ (τ : ℕ) (p : P) : E.st A (τ + 1) p = A.step p (E.st A τ p) (E.inbox A τ p) := rfl

/-- `p` decides `v` at some time. -/
def Decides (p : P) (v : VO) : Prop := ∃ τ, A.decide p (E.st A τ p) = some v

/-- `F` is a legal set of omission-faulty processes for `E`. -/
def Admits (F : Finset P) : Prop :=
  ∀ τ q p, E.ok τ q p = false → A.send q (E.st A τ q) p ≠ [] → q ≠ p ∧ (q ∈ F ∨ p ∈ F)

/-- The input configuration of `E` when `F` is the faulty set. -/
def conf (F : Finset P) : Config P VI := fun p => if p ∈ F then none else some (E.inp p)

/-- Number of messages sent by processes outside `F` to other processes during `[0, N)`. -/
def msgsUpTo (F : Finset P) (N : ℕ) : ℕ :=
  ∑ τ ∈ range N, ∑ q ∈ univ.filter (· ∉ F), ∑ p ∈ univ.filter (· ≠ q),
    (A.send q (E.st A τ q) p).length

open Classical in
/-- Processes outside `F` whose non-empty batches to `p` are omitted at some time. -/
noncomputable def dropSenders (F : Finset P) (p : P) : Finset P :=
  univ.filter fun q => q ∉ F ∧ ∃ τ, E.ok τ q p = false ∧ A.send q (E.st A τ q) p ≠ []

variable {A E}

omit [DecidableEq P] [Fintype P] in
theorem Admits.mono {F F' : Finset P} (h : E.Admits A F) (hF : F ⊆ F') : E.Admits A F' := by
  intro τ q p h1 h2
  obtain ⟨hne, h3⟩ := h τ q p h1 h2
  exact ⟨hne, h3.imp (fun h => hF h) (fun h => hF h)⟩

omit [DecidableEq P] [Fintype P] in
theorem Admits.self (h : E.Admits A F) (τ : ℕ) (q : P) :
    E.inbox A τ q q = A.send q (E.st A τ q) q := by
  unfold inbox
  split_ifs with hok
  · rfl
  · by_contra hne
    exact (h τ q q (by simpa using hok) (Ne.symm hne)).1 rfl

omit [DecidableEq P] [Fintype P] in
theorem inbox_eq_send_of_correct {F : Finset P} (h : E.Admits A F) {τ : ℕ} {q p : P}
    (hq : q ∉ F) (hp : p ∉ F) : E.inbox A τ p q = A.send q (E.st A τ q) p := by
  unfold inbox
  split_ifs with hok
  · rfl
  · by_contra hne
    rcases (h τ q p (by simpa using hok) (Ne.symm hne)).2 with h' | h'
    · exact hq h'
    · exact hp h'

/-- **Swapping omissions** (cf. Lemma 15 of [CivitEtAl2024]).
If `p` omits no non-empty batch to a process outside `F \ {p}`, then the senders of the batches
omitted at `p` can be blamed instead of `p`: `(F \ {p}) ∪ dropSenders F p` is admissible. -/
theorem Admits.swap {F : Finset P} (h : E.Admits A F) {p : P}
    (hp : ∀ τ r, E.ok τ p r = false → A.send p (E.st A τ p) r ≠ [] → r ∈ F) :
    E.Admits A (F.erase p ∪ E.dropSenders A F p) := by
  intro τ q r h1 h2
  obtain ⟨hne, h3⟩ := h τ q r h1 h2
  refine ⟨hne, ?_⟩
  by_cases hr : r = p
  · subst hr
    by_cases hq : q ∈ F
    · exact Or.inl (mem_union_left _ (mem_erase.mpr ⟨hne, hq⟩))
    · refine Or.inl (mem_union_right _ ?_)
      simp only [dropSenders, ne_eq, mem_filter, mem_univ, hq, not_false_eq_true, true_and]
      exact ⟨τ, h1, h2⟩
  · by_cases hq : q = p
    · subst hq
      exact Or.inr (mem_union_left _ (mem_erase.mpr ⟨hr, hp τ r h1 h2⟩))
    · rcases h3 with h3 | h3
      · exact Or.inl (mem_union_left _ (mem_erase.mpr ⟨hq, h3⟩))
      · exact Or.inr (mem_union_left _ (mem_erase.mpr ⟨hr, h3⟩))

theorem not_mem_dropSenders {F : Finset P} {p : P} (hp : p ∈ F) : p ∉ E.dropSenders A F p := by
  simp [dropSenders, hp]

theorem dropSenders_disjoint (F : Finset P) (p : P) : Disjoint (E.dropSenders A F p) F := by
  rw [disjoint_left]; intro q hq; simp only [dropSenders, mem_filter] at hq; exact hq.2.1

omit [DecidableEq P] [Fintype P] in
theorem inbox_congr {E E' : OmExec P VI} {τ : ℕ} {p q : P} (h1 : E.ok τ q p = E'.ok τ q p)
    (h2 : E.ok τ q p = true → E.st A τ q = E'.st A τ q) : E.inbox A τ p q = E'.inbox A τ p q := by
  unfold inbox
  rw [← h1]
  split_ifs with h
  · rw [h2 h]
  · rfl

omit [DecidableEq P] [Fintype P] in
/-- **Indistinguishability.** If the processes of `X (τ+1) ⊆ X τ` get the same inboxes at time
`τ` (given that `X τ` had the same states), they have the same states. -/
theorem st_eq_of_inbox_eq {E E' : OmExec P VI} {X : ℕ → Set P}
    (hX : ∀ τ, X (τ + 1) ⊆ X τ) (h0 : ∀ p ∈ X 0, E.inp p = E'.inp p)
    (hin : ∀ τ, (∀ q ∈ X τ, E.st A τ q = E'.st A τ q) →
      ∀ p ∈ X (τ + 1), E.inbox A τ p = E'.inbox A τ p) :
    ∀ τ, ∀ p ∈ X τ, E.st A τ p = E'.st A τ p := by
  intro τ
  induction τ with
  | zero => intro p hp; simp [h0 p hp]
  | succ τ ih =>
    intro p hp
    rw [st_succ, st_succ, ih p (hX τ hp), hin τ ih p hp]

/-! ### Counting -/

open Classical in
/-- Counting lemma: if `X` and `Y` are disjoint, then within some finite time the processes of `X`
send to processes other than themselves at least as many messages as there are pairs
`(q, p) ∈ X × Y` such that `q` sends something to `p` at some time. -/
theorem count_pairs (X Y : Finset P) (hXY : Disjoint X Y) (f : ℕ → P → P → ℕ) :
    ∃ N, ∑ p ∈ Y, (X.filter fun q => ∃ τ, f τ q p ≠ 0).card ≤
      ∑ τ ∈ range N, ∑ q ∈ X, ∑ p ∈ univ.filter (· ≠ q), f τ q p := by
  let τ₀ : P × P → ℕ := fun qp => if hh : ∃ τ, f τ qp.1 qp.2 ≠ 0 then Classical.choose hh else 0
  let N := (univ : Finset (P × P)).sup τ₀ + 1
  refine ⟨N, ?_⟩
  have key : ∀ q p, (if ∃ τ, f τ q p ≠ 0 then 1 else 0) ≤ ∑ τ ∈ range N, f τ q p := by
    intro q p
    split_ifs with hh
    · have hlt : τ₀ (q, p) < N := Nat.lt_succ_of_le (le_sup (f := τ₀) (mem_univ (q, p)))
      have hτ : τ₀ (q, p) = Classical.choose hh := by simp [τ₀, hh]
      calc 1 ≤ f (τ₀ (q, p)) q p := by
              rw [hτ]; exact Nat.one_le_iff_ne_zero.mpr (Classical.choose_spec hh)
        _ ≤ ∑ τ ∈ range N, f τ q p :=
              single_le_sum (f := fun τ => f τ q p) (fun _ _ => Nat.zero_le _) (mem_range.mpr hlt)
    · exact Nat.zero_le _
  calc ∑ p ∈ Y, (X.filter fun q => ∃ τ, f τ q p ≠ 0).card
      = ∑ p ∈ Y, ∑ q ∈ X, (if ∃ τ, f τ q p ≠ 0 then 1 else 0) := by
        refine sum_congr rfl fun p _ => ?_
        rw [card_eq_sum_ones, sum_filter]
    _ = ∑ q ∈ X, ∑ p ∈ Y, (if ∃ τ, f τ q p ≠ 0 then 1 else 0) := sum_comm
    _ ≤ ∑ q ∈ X, ∑ p ∈ univ.filter (· ≠ q), ∑ τ ∈ range N, f τ q p := by
        refine sum_le_sum fun q hq => ?_
        calc ∑ p ∈ Y, (if ∃ τ, f τ q p ≠ 0 then 1 else 0)
            ≤ ∑ p ∈ Y, ∑ τ ∈ range N, f τ q p := sum_le_sum fun p _ => key q p
          _ ≤ ∑ p ∈ univ.filter (· ≠ q), ∑ τ ∈ range N, f τ q p := by
              refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => Nat.zero_le _
              refine mem_filter.mpr ⟨mem_univ _, fun h => ?_⟩
              subst h
              exact disjoint_left.mp hXY hq hp
    _ = ∑ τ ∈ range N, ∑ q ∈ X, ∑ p ∈ univ.filter (· ≠ q), f τ q p := by
        rw [Finset.sum_comm (s := range N)]
        refine sum_congr rfl fun q _ => ?_
        rw [Finset.sum_comm (s := range N)]

/-- Within some finite time, correct processes send at least `∑_{p ∈ Y} |dropSenders F p|`
messages, for `Y ⊆ F`. -/
theorem sum_card_dropSenders_le {F Y : Finset P} (hY : Y ⊆ F) :
    ∃ N, ∑ p ∈ Y, (E.dropSenders A F p).card ≤ E.msgsUpTo A F N := by
  classical
  obtain ⟨N, hN⟩ := count_pairs (univ.filter (· ∉ F)) Y
    (by
      rw [disjoint_left]; intro q hq hq'
      simp only [mem_filter, mem_univ, true_and] at hq; exact hq (hY hq'))
    (fun τ q p => (A.send q (E.st A τ q) p).length)
  refine ⟨N, le_trans (sum_le_sum fun p _ => card_le_card ?_) hN⟩
  intro q hq
  simp only [dropSenders, mem_filter, mem_univ, true_and] at hq ⊢
  obtain ⟨hqF, τ, -, hne⟩ := hq
  exact ⟨hqF, τ, by simpa using hne⟩

/-! ### Omission executions are Byzantine runs -/

variable (A E)

/-- The Byzantine synchronous run simulating `E` with faulty set `F`. -/
def toRun (F : Finset P) : Run P M VI where
  faulty := F
  inp := E.inp
  gst := 0
  byz q τ p := E.inbox A τ p q
  dl _ τ _ := τ

variable {A E}

omit [Fintype P] in
theorem toRun_st {F : Finset P}
    (hF : ∀ τ q p, q ∉ F → p ∉ F → E.ok τ q p = false → A.send q (E.st A τ q) p = []) :
    ∀ τ, ∀ p ∉ F, (E.toRun A F).st A τ p = E.st A τ p := by
  intro τ
  induction τ with
  | zero => intro p _; rfl
  | succ τ ih =>
    intro p hp
    rw [Run.st_succ, st_succ, ih p hp]
    congr 1
    funext q
    rw [Run.inbox_of_dl_eq A (fun _ _ _ => rfl)]
    by_cases hq : q ∈ F
    · rw [Run.out_of_faulty A _ hq]; rfl
    · rw [Run.out_of_correct A _ hq, ih q hq]
      unfold inbox
      split_ifs with hok
      · rfl
      · exact hF τ q p hq hp (by simpa using hok)

omit [DecidableEq P] [Fintype P] in
theorem Admits.toRun_cond {F : Finset P} (h : E.Admits A F) :
    ∀ τ q p, q ∉ F → p ∉ F → E.ok τ q p = false → A.send q (E.st A τ q) p = [] := by
  intro τ q p hq hp hok
  by_contra hne
  rcases (h τ q p hok hne).2 with h' | h'
  · exact hq h'
  · exact hp h'

omit [Fintype P] in
theorem toRun_inbox {F : Finset P}
    (hF : ∀ τ q p, q ∉ F → p ∉ F → E.ok τ q p = false → A.send q (E.st A τ q) p = [])
    {p : P} (hp : p ∉ F) (τ : ℕ) (q : P) : (E.toRun A F).inbox A p τ q = E.inbox A τ p q := by
  rw [Run.inbox_of_dl_eq A (fun _ _ _ => rfl)]
  by_cases hq : q ∈ F
  · rw [Run.out_of_faulty A _ hq]; rfl
  · rw [Run.out_of_correct A _ hq, toRun_st hF τ q hq]
    unfold inbox
    split_ifs with hok
    · rfl
    · exact hF τ q p hq hp (by simpa using hok)

omit [Fintype P] in
theorem toRun_out_of_correct {F : Finset P} (h : E.Admits A F) {q : P} (hq : q ∉ F) (τ : ℕ)
    (p : P) : (E.toRun A F).out A q τ p = A.send q (E.st A τ q) p := by
  rw [Run.out_of_correct A _ hq, toRun_st h.toRun_cond τ q hq]

omit [DecidableEq P] [Fintype P] in
theorem toRun_valid {F : Finset P} {t : ℕ} (hF : F.card ≤ t) (δ : ℕ) :
    (E.toRun A F).Valid t δ :=
  ⟨hF, fun _ _ _ _ _ => le_rfl, fun _ τ _ _ _ => by simp [toRun]⟩

omit [Fintype P] in
theorem toRun_decides {F : Finset P} (h : E.Admits A F) {p : P} (hp : p ∉ F) {v : VO} :
    (E.toRun A F).Decides A p v ↔ E.Decides A p v := by
  simp only [Run.Decides, Decides, toRun_st h.toRun_cond _ p hp]

omit [Fintype P] in
theorem toRun_inputConf (F : Finset P) : (E.toRun A F).inputConf = E.conf F := rfl

theorem toRun_msgsUpTo {F : Finset P} (h : E.Admits A F) (N : ℕ) :
    (E.toRun A F).msgsUpTo A N = E.msgsUpTo A F N := by
  simp only [Run.msgsUpTo, Run.msgsAt, msgsUpTo]
  refine sum_congr (by simp [toRun]) fun τ _ => sum_congr rfl fun q hq => sum_congr rfl
    fun p _ => ?_
  rw [toRun_out_of_correct h (by simpa using hq)]

/-- The states of `E` are states of runs: `p` has its `E`-state in the run where everybody else
is Byzantine and sends `p` what it receives in `E`. -/
theorem view_st (h : E.Admits A F) (p : P) (τ : ℕ) :
    (E.toRun A {p}ᶜ).st A τ p = E.st A τ p := by
  refine toRun_st (fun τ q r hq hr hok => ?_) τ p (by simp)
  simp only [mem_compl, mem_singleton, not_not] at hq hr
  subst hq; subst hr
  by_contra hne
  exact (h τ _ _ hok hne).1 rfl

set_option linter.unusedFintypeInType false in
/-- Unforgeability in omission executions: a process only sends its own tokens and tokens it
has received before. -/
theorem unforging_om {Au : Auth P M K} (hU : A.Unforging Au) {F : Finset P} (h : E.Admits A F)
    (q : P) (τ : ℕ) (r : P) : ∀ m ∈ A.send q (E.st A τ q) r, ∀ x ∈ Au.tokens m,
      Au.signer x = q ∨ ∃ τ' < τ, ∃ q', ∃ m' ∈ E.inbox A τ' q q', x ∈ Au.tokens m' := by
  intro m hm x hx
  rw [← view_st h q τ] at hm
  rcases hU _ q τ r m hm x hx with hs | ⟨τ', hτ', q', m', hm', hx'⟩
  · exact Or.inl hs
  · refine Or.inr ⟨τ', hτ', q', m', ?_, hx'⟩
    rwa [toRun_inbox (fun τ q r hq hr hok => ?_) (by simp)] at hm'
    simp only [mem_compl, mem_singleton, not_not] at hq hr
    subst hq; subst hr
    by_contra hne
    exact (h τ _ _ hok hne).1 rfl

set_option linter.unusedFintypeInType false in
/-- The simulating run respects unforgeability: tokens in messages of `E` are signed by faulty
processes or were emitted (as genuine messages) by correct processes by then. -/
theorem toRun_authValid {Au : Auth P M K} (hU : A.Unforging Au) {F : Finset P}
    (h : E.Admits A F) : (E.toRun A F).AuthValid Au A := by
  have main : ∀ σ q r, ∀ m ∈ A.send q (E.st A σ q) r, ∀ x ∈ Au.tokens m,
      Au.signer x ∈ F ∨ x ∈ (E.toRun A F).honestTokens Au A σ := by
    intro σ
    induction σ using Nat.strong_induction_on with
    | _ σ ih =>
      intro q r m hm x hx
      rcases unforging_om hU h q σ r m hm x hx with hs | ⟨τ', hτ', q', m', hm', hx'⟩
      · by_cases hq : q ∈ F
        · exact Or.inl (hs ▸ hq)
        · exact Or.inr ⟨σ, le_rfl, q, hq, r, m, by rw [toRun_out_of_correct h hq]; exact hm, hx⟩
      · unfold inbox at hm'
        split_ifs at hm' with hok
        · rcases ih τ' hτ' q' q m' hm' x hx' with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Run.honestTokens_mono hτ'.le h1)
        · simp at hm'
  intro b _ τ r _ m hm x hx
  change m ∈ E.inbox A τ r b at hm
  unfold inbox at hm
  split_ifs at hm
  · exact main τ b r m hm x hx
  · simp at hm

/-! ### Specification -/

/-- `A` solves consensus with `val` in the synchronous **omission** model with at most `t`
omission-faulty processes. -/
structure _root_.Cslib.Byzantine.PartialSync.OmSolves (t : ℕ) (A : Algorithm P M S VI VO)
    (val : ValidityProperty P VI VO) : Prop where
  termination : ∀ (E : OmExec P VI) (F : Finset P), E.Admits A F → F.card ≤ t →
    ∀ p ∉ F, ∃ v, E.Decides A p v
  agreement : ∀ (E : OmExec P VI) (F : Finset P), E.Admits A F → F.card ≤ t →
    ∀ p ∉ F, ∀ q ∉ F, ∀ v w, E.Decides A p v → E.Decides A q w → v = w
  validity : ∀ (E : OmExec P VI) (F : Finset P), E.Admits A F → F.card ≤ t →
    ∀ p ∉ F, ∀ v, E.Decides A p v → v ∈ val (E.conf F)

end OmExec

set_option linter.unusedFintypeInType false in
/-- Every synchronous Byzantine solution (authenticated, unforging) is an omission solution. -/
theorem SolvesConsensusAuthSync.omSolves {t δ : ℕ} {A : Algorithm P M S VI VO}
    {val : ValidityProperty P VI VO} {Au : Auth P M K} (hU : A.Unforging Au)
    (hA : SolvesConsensusAuthSync Au t δ A val) : OmSolves t A val where
  termination E F h hF p hp := by
    obtain ⟨v, hv⟩ := hA.termination _ (OmExec.toRun_valid hF δ) (OmExec.toRun_authValid hU h)
      rfl p hp
    exact ⟨v, (OmExec.toRun_decides h hp).mp hv⟩
  agreement E F h hF p hp q hq v w hv hw :=
    hA.agreement _ (OmExec.toRun_valid hF δ) (OmExec.toRun_authValid hU h) rfl p hp q hq v w
      ((OmExec.toRun_decides h hp).mpr hv) ((OmExec.toRun_decides h hq).mpr hw)
  validity E F h hF p hp v hv :=
    hA.validity _ (OmExec.toRun_valid hF δ) (OmExec.toRun_authValid hU h) rfl p hp v
      ((OmExec.toRun_decides h hp).mpr hv)

set_option linter.unusedFintypeInType false in
/-- Every synchronous Byzantine solution is an omission solution. -/
theorem SolvesConsensusSync.omSolves {t δ : ℕ} {A : Algorithm P M S VI VO}
    {val : ValidityProperty P VI VO} (hA : SolvesConsensusSync t δ A val) : OmSolves t A val :=
  SolvesConsensusAuthSync.omSolves A.unforging_none hA

end Cslib.Byzantine.PartialSync

/-! ### Standard omission executions -/

namespace Cslib.Byzantine.PartialSync

open Finset

variable {P M S VI VO : Type*}

namespace OmExec

/-- The fault-free omission execution with inputs `x`. -/
def ff (x : P → VI) : OmExec P VI where
  inp := x
  ok _ _ _ := true

/-- The omission execution with inputs `x` in which every process of `B` is isolated: it receives
only its own messages. -/
def solo [DecidableEq P] (x : P → VI) (B : Finset P) : OmExec P VI where
  inp := x
  ok _ q p := !decide (p ∈ B ∧ q ≠ p)

variable {A : Algorithm P M S VI VO} {x : P → VI}

@[simp] theorem ff_inp : (ff x).inp = x := rfl
@[simp] theorem ff_ok (τ : ℕ) (q p : P) : (ff x).ok τ q p = true := rfl

/-- Every faulty set is admissible for the fault-free execution. -/
theorem ff_admits (F : Finset P) : (ff x).Admits A F := fun _ _ _ h => by simp at h

@[simp] theorem ff_inbox (τ : ℕ) (p q : P) :
    (ff x).inbox A τ p q = A.send q ((ff x).st A τ q) p := rfl

section solo

variable [DecidableEq P] {B : Finset P}

@[simp] theorem solo_inp : (solo x B).inp = x := rfl

theorem solo_ok (τ : ℕ) (q p : P) : (solo x B).ok τ q p = !decide (p ∈ B ∧ q ≠ p) := rfl

/-- In `solo x B`, the processes of `B` are a legal set of omission-faulty processes. -/
theorem solo_admits : (solo x B).Admits A B := by
  intro τ q p h _
  simp only [solo_ok, Bool.not_eq_false', decide_eq_true_eq] at h
  exact ⟨h.2, Or.inr h.1⟩

/-- An isolated process receives nothing from the other processes. -/
theorem solo_inbox_of_mem {p q : P} (hp : p ∈ B) (hq : q ≠ p) (τ : ℕ) :
    (solo x B).inbox A τ p q = [] := by
  simp [inbox, solo_ok, hp, hq]

/-- An isolated process behaves as in any other execution in which it is isolated with the same
input. -/
theorem solo_st {y : P → VI} {C : Finset P} {p : P} (hpB : p ∈ B) (hpC : p ∈ C)
    (hxy : x p = y p) (τ : ℕ) : (solo x B).st A τ p = (solo y C).st A τ p := by
  refine st_eq_of_inbox_eq (X := fun _ => {p}) (fun _ => le_rfl)
    (fun q hq => by rw [Set.mem_singleton_iff.mp hq]; exact hxy) (fun τ ih q hq => ?_) τ p rfl
  rw [Set.mem_singleton_iff.mp hq]
  funext r
  refine inbox_congr ?_ fun hok => ?_
  · by_cases hr : r = p <;> simp [solo_ok, hpB, hpC, hr]
  · by_cases hr : r = p
    · subst hr; exact ih r rfl
    · simp [solo_ok, hpB, hr] at hok

end solo

end OmExec

namespace Run

variable [DecidableEq P] {A : Algorithm P M S VI VO}

/-- A fault-free run with zero delays has the states of the fault-free omission execution. -/
theorem st_eq_ff {R : Run P M VI} (hf : R.faulty = ∅) (hdl : ∀ q τ p, R.dl q τ p = τ) :
    R.st A = (OmExec.ff R.inp).st A := by
  funext τ
  induction τ with
  | zero => rfl
  | succ τ ih =>
    funext p
    rw [st_succ, OmExec.st_succ, ih]
    congr 1
    funext q
    rw [inbox_of_dl_eq A hdl, out_of_correct A _ (by simp [hf]), ih, OmExec.ff_inbox]

/-- The quiet fault-free run decides as the fault-free omission execution. -/
theorem quiet_empty_decides_iff {x : P → VI} {p : P} {v : VO} :
    (quiet (M := M) ∅ x).Decides A p v ↔ (OmExec.ff x).Decides A p v := by
  simp only [Decides, OmExec.Decides, st_eq_ff (R := quiet (M := M) ∅ x) rfl (fun _ _ _ => rfl),
    quiet_inp]

end Run

end Cslib.Byzantine.PartialSync
