/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Linearization
public import Cslib.Computability.Distributed.SharedMemory.Progress

/-!
# A linearizability criterion for single-writer single-reader registers

For an execution `α` of an implementation of `register V v₀` in which only process `w` writes
and only process `r` reads, linearizability follows from a *reads-from* assignment
`rf : ℕ → ℕ` for the reader's completed operations: `rf k = m` means that the `k`-th read of `r`
(0-based) reads the value of the `m`-th write of `w` (1-based: `m = 0` is the initial value
`v₀`, `m = j + 1` is the write `(w, j)`).

**Main statement** (`SWSRReadsFrom.isLinearization`): if `SWSRReadsFrom α w r rf`, i.e.

* `w ≠ r`, the history of `α` is well formed, `w` only invokes writes, `r` only invokes reads,
  no other process invokes anything (`ops`),
* a completed write returns the written value (`write_resp`),
* for every completed read `k`:
  - it returns the value of write `rf k` (`read_val`, via `writeVal`),
  - it does not read from the future: it does not return before write `rf k` (that is,
    `(w, rf k - 1)`) is invoked (`not_future`),
  - it does not read an overwritten value: write `rf k + 1` (that is, `(w, rf k)`) does not
    return before the read is invoked (`not_overwritten`),
* there is no new-old inversion: if read `k` precedes read `k'` then `rf k ≤ rf k'` (`mono`),

then `swsrLin α w r rf` is a linearization of `α`. It consists of all invoked writes in program
order, and the completed reads, each placed right after the write it reads from (reads from the
same write ordered by index). Its final state is the value of the last invoked write
(`linState_swsrLin`).

`Impl.isLinFun_swsrLin` packages this for implementations.

Auxiliary general facts about real-time order: `WellFormed.resps_le_ops`, `Precedes.trans`,
`Precedes.of_append_of_invoked` (stability of `¬ Precedes α a b` once `b` is invoked),
`Precedes.lt_of_proc` (program order), `Impl.allowed_of_mem_opsOf`.

-/

@[expose] public section

namespace Cslib.SharedMemory

open List

variable {P : Type} [DecidableEq P] {A : ObjSpec}

/-! ## General facts on histories -/

/-- In a well-formed history, every prefix has at most one more invocation than responses per
process, and at least as many. -/
lemma WellFormed.counts {α β γ : List (Label P A)} (hα : WellFormed α) (h : α = β ++ γ) (p : P) :
    (respsOf β p).length ≤ (opsOf β p).length ∧
      (opsOf β p).length ≤ (respsOf β p).length + 1 := by
  induction β using List.reverseRecOn generalizing γ with
  | nil => simp
  | append_singleton β ℓ ih =>
    have ih' := ih (γ := ℓ :: γ) (by simp [h])
    have hwf := hα β ℓ γ (by simp [h]) p
    simp only [opsOf_append, respsOf_append, opsOf_cons, respsOf_cons, opsOf_nil, respsOf_nil,
      List.append_nil, List.length_append]
    cases ℓ with
    | inv q o =>
      by_cases hq : q = p
      · subst hq; have := hwf.1 (by simp); simp; omega
      · simp [hq]; omega
    | ret q x =>
      by_cases hq : q = p
      · subst hq; have := hwf.2 (by simp); simp; omega
      · simp [hq]; omega
    | tau q => simp; omega

lemma WellFormed.resps_le_ops {α : List (Label P A)} (hα : WellFormed α) (p : P) :
    (respsOf α p).length ≤ (opsOf α p).length :=
  (hα.counts (γ := []) (by simp) p).1

/-- A completed operation has been invoked (well-formed histories). -/
lemma WellFormed.invoked_of_completed {α : List (Label P A)} (hα : WellFormed α) {x : OpId P}
    (h : Completed α x) : Invoked α x :=
  lt_of_lt_of_le h (hα.resps_le_ops x.1)

/-- Real-time order is transitive (well-formed histories). -/
lemma Precedes.trans {α : List (Label P A)} (hα : WellFormed α) {a b c : OpId P}
    (h₁ : Precedes α a b) (h₂ : Precedes α b c) : Precedes α a c := by
  obtain ⟨β₁, γ₁, e₁, ha, hb⟩ := h₁
  obtain ⟨β₂, γ₂, e₂, hb', hc⟩ := h₂
  have hb'' : Invoked β₂ b := (hα.counts e₂ b.1).1.trans_lt' hb'
  rcases List.prefix_or_prefix_of_prefix (l₃ := α) ⟨γ₁, e₁.symm⟩ ⟨γ₂, e₂.symm⟩ with hp | hp
  · obtain ⟨δ, rfl⟩ := hp
    exact ⟨_, γ₂, e₂, ha.mono, hc⟩
  · obtain ⟨δ, rfl⟩ := hp
    exact absurd hb''.mono hb

/-- If `b` is invoked in `α ++ γ` and `a` precedes `b` there, then `a` has completed... at the
latest when `b` is invoked; in particular, if `b` is not invoked in `α`, the response of `a` is
in `α ++ γ` before `b`'s invocation. Special case used most often: `γ = [ℓ]`. -/
lemma Precedes.completed_of_append_singleton {α : List (Label P A)} {ℓ : Label P A}
    {a b : OpId P} (h : Precedes (α ++ [ℓ]) a b) (hb : Invoked (α ++ [ℓ]) b) :
    Completed α a := by
  obtain ⟨β, γ', e, ha, hnb⟩ := h
  rcases List.prefix_or_prefix_of_prefix (l₃ := α ++ [ℓ]) ⟨γ', e.symm⟩ (List.prefix_append α [ℓ])
    with hp | hp
  · obtain ⟨δ, rfl⟩ := hp
    exact ha.mono
  · obtain ⟨δ, hδ⟩ := hp
    rcases δ with _ | ⟨x, δ⟩
    · simp only [append_nil] at hδ; subst hδ; exact ha
    · have : β = α ++ [ℓ] := by
        have hl := congrArg List.length e
        have hl2 := congrArg List.length hδ
        simp at hl hl2
        obtain ⟨γ'', rfl⟩ : ∃ γ'', γ' = γ'' := ⟨_, rfl⟩
        have : γ' = [] := by
          rw [← List.length_eq_zero_iff]; omega
        simpa [this] using e.symm
      subst this; exact absurd hb hnb

/-- Program order: an operation of `p` can only precede later operations of `p`. -/
lemma Precedes.lt_of_proc {α : List (Label P A)} (hα : WellFormed α) {p : P} {i j : ℕ}
    (h : Precedes α (p, i) (p, j)) : i < j := by
  obtain ⟨β, γ, e, hi, hj⟩ := h
  have := (hα.counts e p).1
  simp only [Completed, Invoked] at hi hj
  omega

/-- Every operation invoked in an execution is allowed. -/
lemma Impl.allowed_of_mem_opsOf {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}
    (I : Impl A B P L) {α : List (Label P A)} (hα : I.Valid α) {p : P} {o : A.Op}
    (ho : o ∈ opsOf α p) : I.allowed p o := by
  induction α using List.reverseRecOn with
  | nil => simp at ho
  | append_singleton α ℓ ih =>
    obtain ⟨C, hC⟩ := hα
    obtain ⟨C₁, h1, h2⟩ := I.runFrom_eq_some_of_append hC
    rw [Impl.runFrom_singleton] at h2
    rw [opsOf_append, List.mem_append] at ho
    rcases ho with ho | ho
    · exact ih ⟨C₁, h1⟩ ho
    · cases ℓ with
      | inv q o' =>
        by_cases hq : q = p
        · subst hq
          simp only [opsOf_cons, Label.invOf_inv, ↓reduceIte, Option.toList_some, opsOf_nil,
            append_nil, mem_cons, not_mem_nil, or_false] at ho
          subst ho; exact (Impl.step_inv h2).2.1
        · simp [hq] at ho
      | ret q x => simp at ho
      | tau q => simp at ho

/-! ## Values of a sequence of writes -/

variable {V : Type} {v₀ : V}

/-- The value of `register V v₀` after the first `m` operations of `ws` (in our use: the
writes of the writer); `writeVal v₀ ws 0 = v₀`. -/
def writeVal (v₀ : V) (ws : List (RWOp V)) (m : ℕ) : V :=
  (register V v₀).runOps v₀ (ws.take m)

@[simp] lemma writeVal_zero (ws : List (RWOp V)) : writeVal v₀ ws 0 = v₀ := rfl

lemma writeVal_succ {ws : List (RWOp V)} {m : ℕ} {v : V} (h : ws[m]? = some (.write v)) :
    writeVal v₀ ws (m + 1) = v := by
  simp only [writeVal, List.take_add_one, h, Option.toList_some]
  simp [ObjSpec.runOps]

lemma writeVal_append_of_le {ws ws' : List (RWOp V)} {m : ℕ} (h : m ≤ ws.length) :
    writeVal v₀ (ws ++ ws') m = writeVal v₀ ws m := by
  simp [writeVal, List.take_append, Nat.sub_eq_zero_of_le h]

/-! ## The linearization -/

/-- The completed reads (among the first `nR` reads of `r`) that read from write `m`. -/
def swsrReads (r : P) (rf : ℕ → ℕ) (nR m : ℕ) : List (OpId P × RWOp V) :=
  ((range nR).filter (fun k => rf k = m)).map (fun k => ((r, k), RWOp.read))

/-- The first `j` writes, each followed by the reads that read from it (preceded by the reads
from the initial value). -/
def swsrLinAux (w r : P) (ws : List (RWOp V)) (rf : ℕ → ℕ) (nR : ℕ) :
    ℕ → List (OpId P × RWOp V)
  | 0 => swsrReads r rf nR 0
  | j + 1 => swsrLinAux w r ws rf nR j ++ ((w, j), ws.getD j .read) :: swsrReads r rf nR (j + 1)

/-- The reads-from linearization of `α`: all invoked writes of `w` in program order; every
completed read `k` of `r` right after write `rf k`; reads from the same write by index. -/
def swsrLin (α : List (Label P (register V v₀))) (w r : P) (rf : ℕ → ℕ) :
    List (OpId P × RWOp V) :=
  swsrLinAux w r (opsOf α w) rf (respsOf α r).length (opsOf α w).length

/-- Hypotheses of the reads-from criterion (see the module docstring). -/
structure SWSRReadsFrom (α : List (Label P (register V v₀))) (w r : P) (rf : ℕ → ℕ) : Prop where
  ne : w ≠ r
  wellFormed : WellFormed α
  ops : ∀ p, ∀ o ∈ opsOf α p, RWOp.SWSR w r p o
  write_resp : ∀ j v x, opOf α (w, j) = some (.write v) → respOf α (w, j) = some x → x = v
  read_val : ∀ k < (respsOf α r).length,
    respOf α (r, k) = some (writeVal v₀ (opsOf α w) (rf k))
  not_future : ∀ k < (respsOf α r).length, 0 < rf k → ¬ Precedes α (r, k) (w, rf k - 1)
  not_overwritten : ∀ k < (respsOf α r).length, ¬ Precedes α (w, rf k) (r, k)
  mono : ∀ k k', k < k' → k' < (respsOf α r).length → Precedes α (r, k) (r, k') → rf k ≤ rf k'

/-! ### Auxiliary lemmas for the criterion -/

lemma writeVal_succ' (ws : List (RWOp V)) (j : ℕ) :
    writeVal v₀ ws (j + 1) = ((register V v₀).δ (writeVal v₀ ws j) (ws.getD j .read)).1 := by
  simp only [writeVal, List.take_add_one, List.getD_eq_getElem?_getD]
  cases ws[j]? with
  | none => simp
  | some o => simp [ObjSpec.runOps]

/-- A strict order on operation instances used to show that the reads-from linearization
respects real time: writes `(w, i)` get key `2 i + 1`, reads `(r, k)` get key `2 rf(k)`,
ties broken by index. -/
def swsrKey (w : P) (rf : ℕ → ℕ) (x : OpId P) : ℕ := if x.1 = w then 2 * x.2 + 1 else 2 * rf x.2

/-- The strict order of `swsrKey`. -/
def swsrBefore (w : P) (rf : ℕ → ℕ) (x y : OpId P) : Prop :=
  swsrKey w rf x < swsrKey w rf y ∨ (swsrKey w rf x = swsrKey w rf y ∧ x.2 < y.2)

lemma sublist_pair_of_pairwise {X : Type} {R : X → X → Prop} {l : List X} (hl : l.Pairwise R)
    {a b : X} (ha : a ∈ l) (hb : b ∈ l) (hab : R a b) (hba : ¬ R b a) : [a, b].Sublist l := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd hab hba
      · exact List.cons_sublist_cons.2 (List.singleton_sublist.2 hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd (hl.1 a ha') hba
      · exact (ih hl.2 ha' hb').cons x

omit [DecidableEq P] in
lemma mem_swsrReads {r : P} {rf : ℕ → ℕ} {nR m : ℕ} {y : OpId P × RWOp V} :
    y ∈ swsrReads r rf nR m ↔ ∃ k < nR, rf k = m ∧ y = ((r, k), .read) := by
  simp only [swsrReads, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩; exact ⟨k, h1, h2, rfl⟩
  · rintro ⟨k, h1, h2, rfl⟩; exact ⟨k, ⟨h1, h2⟩, rfl⟩

omit [DecidableEq P] in
lemma mem_swsrLinAux {w r : P} {ws : List (RWOp V)} {rf : ℕ → ℕ} {nR : ℕ} (j : ℕ)
    {y : OpId P × RWOp V} :
    y ∈ swsrLinAux w r ws rf nR j ↔
      (∃ i < j, y = ((w, i), ws.getD i .read)) ∨ (∃ k < nR, rf k ≤ j ∧ y = ((r, k), .read)) := by
  induction j with
  | zero =>
    simp only [swsrLinAux, mem_swsrReads, Nat.not_lt_zero, false_and, exists_false, false_or,
      Nat.le_zero]
  | succ j ih =>
    simp only [swsrLinAux, List.mem_append, ih, List.mem_cons, mem_swsrReads]
    constructor
    · rintro ((⟨i, hi, rfl⟩ | ⟨k, hk, hrf, rfl⟩) | rfl | ⟨k, hk, hrf, rfl⟩)
      · exact Or.inl ⟨i, by omega, rfl⟩
      · exact Or.inr ⟨k, hk, by omega, rfl⟩
      · exact Or.inl ⟨j, by omega, rfl⟩
      · exact Or.inr ⟨k, hk, by omega, rfl⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨k, hk, hrf, rfl⟩)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact Or.inl (Or.inl ⟨i, hi, rfl⟩)
        · exact Or.inr (Or.inl rfl)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hrf) with h' | h'
        · exact Or.inl (Or.inr ⟨k, hk, by omega, rfl⟩)
        · exact Or.inr (Or.inr ⟨k, hk, h', rfl⟩)

lemma pairwise_swsrReads {w r : P} (hwr : w ≠ r) (rf : ℕ → ℕ) (nR m : ℕ) :
    (swsrReads (V := V) r rf nR m).Pairwise (fun y z => swsrBefore w rf y.1 z.1) := by
  unfold swsrReads
  rw [List.pairwise_map]
  refine ((List.pairwise_lt_range (n := nR)).sublist List.filter_sublist).imp_of_mem ?_
  intro a b ha hb hab
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  have h1 := ha.2; have h2 := hb.2
  simp only [swsrBefore, swsrKey, Ne.symm hwr, ite_false]
  omega

lemma pairwise_swsrLinAux {w r : P} (hwr : w ≠ r) (ws : List (RWOp V)) (rf : ℕ → ℕ) (nR : ℕ)
    (j : ℕ) : (swsrLinAux w r ws rf nR j).Pairwise (fun y z => swsrBefore w rf y.1 z.1) := by
  induction j with
  | zero => exact pairwise_swsrReads hwr rf nR 0
  | succ j ih =>
    simp only [swsrLinAux]
    rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨ih, ⟨?_, pairwise_swsrReads hwr rf nR _⟩, ?_⟩
    · intro z hz
      obtain ⟨k, -, hk, rfl⟩ := mem_swsrReads.1 hz
      simp only [swsrBefore, swsrKey, Ne.symm hwr, ite_true, ite_false, hk]
      omega
    · intro y hy z hz
      have hy' := (mem_swsrLinAux j).1 hy
      rcases List.mem_cons.1 hz with rfl | hz
      · rcases hy' with ⟨i, hi, rfl⟩ | ⟨k, -, hk, rfl⟩
        · simp only [swsrBefore, swsrKey, ite_true]; omega
        · simp only [swsrBefore, swsrKey, Ne.symm hwr, ite_true, ite_false]; omega
      · obtain ⟨k', -, hk', rfl⟩ := mem_swsrReads.1 hz
        rcases hy' with ⟨i, hi, rfl⟩ | ⟨k, -, hk, rfl⟩
        · simp only [swsrBefore, swsrKey, Ne.symm hwr, ite_true, ite_false, hk']; omega
        · simp only [swsrBefore, swsrKey, Ne.symm hwr, ite_false, hk']; omega

omit [DecidableEq P] in
/-- State reached by the first `j` writes of the reads-from linearization. -/
lemma runOps_swsrLinAux (w r : P) (ws : List (RWOp V)) (rf : ℕ → ℕ) (nR j : ℕ) :
    (register V v₀).runOps v₀ ((swsrLinAux w r ws rf nR j).map Prod.snd) = writeVal v₀ ws j := by
  have hreads : ∀ m q, (register V v₀).runOps q ((swsrReads (V := V) r rf nR m).map Prod.snd) = q :=
    fun m q => ObjSpec.runOps_of_readOnly _ _ _ (by
      intro o ho
      simp only [swsrReads, List.map_map, List.mem_map] at ho
      obtain ⟨_, _, rfl⟩ := ho
      intro q; rfl)
  induction j with
  | zero => simp [swsrLinAux, hreads]
  | succ j ih =>
    rw [swsrLinAux, List.map_append, ObjSpec.runOps_append, ih, List.map_cons,
      ObjSpec.runOps_cons, hreads, writeVal_succ']

lemma seqOK_swsrReads {α : List (Label P (register V v₀))} {r : P} {rf : ℕ → ℕ} {nR m : ℕ}
    {q : V} (h : ∀ k < nR, rf k = m → respOf α (r, k) = some q) :
    SeqOK α q (swsrReads r rf nR m) := by
  unfold swsrReads
  generalize hl : (List.range nR).filter (fun k => rf k = m) = l
  have hl' : ∀ k ∈ l, k < nR ∧ rf k = m := by
    intro k hk; rw [← hl] at hk; simpa using hk
  clear hl
  induction l with
  | nil => trivial
  | cons k l ih =>
    refine ⟨?_, ih (fun k' hk' => hl' k' (by simp [hk']))⟩
    intro x hx
    have := h k (hl' k (by simp)).1 (hl' k (by simp)).2
    rw [this] at hx; cases hx; rfl

/-- **Reads-from criterion.** -/
theorem SWSRReadsFrom.isLinearization {α : List (Label P (register V v₀))} {w r : P}
    {rf : ℕ → ℕ} (h : SWSRReadsFrom α w r rf) : IsLinearization α (swsrLin α w r rf) := by
  have hwr := h.ne
  have hα := h.wellFormed
  have hL : swsrLin α w r rf =
      swsrLinAux w r (opsOf α w) rf (respsOf α r).length (opsOf α w).length := rfl
  rw [hL]
  set ws := opsOf α w with hws
  set nR := (respsOf α r).length with hnR
  -- reads read from invoked writes
  have hrf_le : ∀ k < nR, rf k ≤ ws.length := by
    intro k hk
    by_contra hc
    apply h.not_future k hk (by omega)
    exact ⟨α, [], by simp, hk, by simp only [Invoked, ← hws]; omega⟩
  have hproc : ∀ x : OpId P, Invoked α x → x.1 = w ∨ x.1 = r := by
    intro x hx
    rcases h.ops x.1 _ (List.getElem_mem hx) with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hmem := fun y => mem_swsrLinAux (w := w) (r := r) (ws := ws) (rf := rf) (nR := nR)
    ws.length (y := y)
  have hpw := pairwise_swsrLinAux hwr ws rf nR ws.length
  have hcomplete : ∀ a, Completed α a →
      a ∈ (swsrLinAux w r ws rf nR ws.length).map Prod.fst := by
    rintro ⟨p, k⟩ ha
    rcases hproc _ (hα.invoked_of_completed ha) with hp | hp <;> simp only at hp <;> subst hp
    · exact List.mem_map.2 ⟨((p, k), ws.getD k .read),
        (hmem _).2 (Or.inl ⟨k, hα.invoked_of_completed ha, rfl⟩), rfl⟩
    · exact List.mem_map.2 ⟨((p, k), .read), (hmem _).2 (Or.inr ⟨k, ha, hrf_le k ha, rfl⟩), rfl⟩
  refine ⟨?_, ?_, hcomplete, ?_, ?_⟩
  · -- nodup
    refine (List.pairwise_map.2 hpw).imp ?_
    intro x y hxy heq; subst heq; simp [swsrBefore] at hxy
  · -- operations
    intro y hy
    rcases (hmem y).1 hy with ⟨i, hi, rfl⟩ | ⟨k, hk, -, rfl⟩
    · simp [opOf, ← hws, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    · have hk' : k < (opsOf α r).length := lt_of_lt_of_le hk (hα.resps_le_ops r)
      have hop := h.ops r _ (List.getElem_mem hk')
      rcases hop with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1.symm hwr
      · simp [opOf, List.getElem?_eq_getElem hk', h2]
  · -- real time
    intro a b hab hb
    have ha := hcomplete a hab.completed
    have hbefore : swsrBefore w rf a b := by
      obtain ⟨yb, hyb, rfl⟩ := List.mem_map.1 hb
      have hainv := hα.invoked_of_completed hab.completed
      obtain ⟨p, i⟩ := a
      rcases (hmem yb).1 hyb with ⟨j, hj, rfl⟩ | ⟨k', hk', -, rfl⟩
      · -- b is the write (w, j)
        simp only at hab ⊢
        rcases hproc _ hainv with hp | hp <;> simp only at hp <;> subst hp
        · have := Precedes.lt_of_proc hα hab
          simp only [swsrBefore, swsrKey, ite_true]; omega
        · -- a is the read (r, i)
          have hk : i < nR := hab.completed
          have : rf i ≤ j := by
            by_contra hc
            rcases Nat.lt_or_ge j (rf i - 1) with hlt | hge
            · apply h.not_future i hk (by omega)
              refine Precedes.trans hα hab (hα.precedes_of_lt hlt ?_)
              have := hrf_le i hk; simp only [Invoked, ← hws]; omega
            · have : j = rf i - 1 := by omega
              subst this
              exact h.not_future i hk (by omega) hab
          simp only [swsrBefore, swsrKey, hwr.symm, ite_true, ite_false]; omega
      · -- b is the read (r, k')
        simp only at hab ⊢
        rcases hproc _ hainv with hp | hp <;> simp only at hp <;> subst hp
        · -- a is the write (w, i)
          have : i < rf k' := by
            by_contra hc
            rcases Nat.lt_or_ge (rf k') i with hlt | hge
            · exact h.not_overwritten k' hk' (Precedes.trans hα (hα.precedes_of_lt hlt hainv) hab)
            · have : i = rf k' := by omega
              subst this
              exact h.not_overwritten k' hk' hab
          simp only [swsrBefore, swsrKey, hwr.symm, ite_true, ite_false]; omega
        · have hlt := Precedes.lt_of_proc hα hab
          have := h.mono i k' hlt hk' hab
          simp only [swsrBefore, swsrKey, hwr.symm, ite_false]; omega
    refine sublist_pair_of_pairwise (List.pairwise_map.2 hpw) ha hb hbefore ?_
    intro h'; simp only [swsrBefore] at hbefore h'; omega
  · -- legality
    have hwrite : ∀ j x, respOf α (w, j) = some x →
        ((register V v₀).δ (writeVal v₀ ws j) (ws.getD j .read)).2 = x := by
      intro j x hx
      have hj : j < (respsOf α w).length := (List.getElem?_eq_some_iff.1 hx).1
      have hj' : j < ws.length := lt_of_lt_of_le hj (hα.resps_le_ops w)
      rcases h.ops w _ (List.getElem_mem hj') with ⟨-, v, hv⟩ | ⟨h1, -⟩
      · have := h.write_resp j v x (by simp [opOf, ← hws, List.getElem?_eq_getElem hj', hv]) hx
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some, hv]
        exact this.symm
      · exact absurd h1 hwr
    have hreads : ∀ m, SeqOK α (writeVal v₀ ws m) (swsrReads r rf nR m) := by
      intro m
      apply seqOK_swsrReads
      intro k hk hkm
      rw [h.read_val k hk, hkm]
    suffices ∀ j, SeqOK α v₀ (swsrLinAux w r ws rf nR j) from this _
    intro j
    induction j with
    | zero => exact hreads 0
    | succ j ih =>
      rw [swsrLinAux, seqOK_append, runOps_swsrLinAux]
      refine ⟨ih, hwrite j, ?_⟩
      rw [← writeVal_succ']
      exact hreads (j + 1)

/-- The final state of the reads-from linearization is the value of the last invoked write. -/
theorem linState_swsrLin (α : List (Label P (register V v₀))) (w r : P) (rf : ℕ → ℕ) :
    linState (A := register V v₀) (swsrLin α w r rf) =
      writeVal v₀ (opsOf α w) (opsOf α w).length :=
  runOps_swsrLinAux _ _ _ _ _ _

/-- The reads-from criterion for implementations: if every execution has a reads-from
assignment satisfying `SWSRReadsFrom`, the reads-from linearizations form a linearization
function. -/
theorem Impl.isLinFun_swsrLin {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}
    (I : Impl (register V v₀) B P L) (w r : P) (rf : List (Label P (register V v₀)) → ℕ → ℕ)
    (h : ∀ α, I.Valid α → SWSRReadsFrom α w r (rf α)) :
    I.IsLinFun (fun α => swsrLin α w r (rf α)) :=
  fun α hα => (h α hα).isLinearization

end Cslib.SharedMemory
