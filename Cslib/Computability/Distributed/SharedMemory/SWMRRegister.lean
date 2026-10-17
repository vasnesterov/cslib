/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.SWSRRegister
public import Cslib.Computability.Distributed.SharedMemory.LinPoints

/-!
# A linearizability criterion for single-writer multi-reader registers

For a history `α` of `register V v₀` in which only process `w` writes (and `w` does not read)
while any other process may read, linearizability follows from a *reads-from* assignment
`rf : OpId P → ℕ` on the completed reads: `rf x = m` means that read `x` returns the value of the
`m`-th write of `w` (1-based; `m = 0` is the initial value `v₀`, `m = j + 1` is the write
`(w, j)`).

**Main statement** (`SWMRReadsFrom.isLinearization`): if `SWMRReadsFrom α w rf`, i.e.

* the history is well formed, `w` only invokes writes, other processes only invoke reads (`ops`),
* a completed write returns the written value (`write_resp`),
* every completed read `x` returns the value of write `rf x` (`read_val`), does not read from the
  future (`not_future`: it does not return before write `rf x` is invoked) and does not read an
  overwritten value (`not_overwritten`: write `rf x + 1` does not return before `x` is invoked),
* there is no new–old inversion (`mono`: if read `x` precedes read `y` then `rf x ≤ rf y`),

then `swmrLin α w rf` is a linearization of `α`: all invoked writes in program order, every
completed read right after the write it reads from, reads from the same write in invocation
order. These are exactly the three "claims" used in atomicity proofs of SWMR register
algorithms (e.g. Lemma 10 of Mostéfaoui–Raynal, PODC 2016).

The invocation order `invIds α` (with `Precedes.sublist_invIds`: real-time order implies
invocation order) and `Precedes.not_of_invoked` are in `History.lean`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

open List

variable {P : Type} [DecidableEq P] {A : ObjSpec}

@[deprecated not_sublist_pair_both (since := "2026-10-18")]
alias sublist_pair_asymm := not_sublist_pair_both

lemma pairwise_sublist_self {X : Type} (l : List X) : l.Pairwise (fun x y => [x, y].Sublist l) := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [pairwise_cons]
    refine ⟨fun y hy => List.cons_sublist_cons.2 (List.singleton_sublist.2 hy), ?_⟩
    exact ih.imp (fun h => h.cons c)

/-! ## The linearization -/

instance (α : List (Label P A)) (x : OpId P) : Decidable (Completed α x) :=
  inferInstanceAs (Decidable (_ < _))

instance (α : List (Label P A)) (x : OpId P) : Decidable (Invoked α x) :=
  inferInstanceAs (Decidable (_ < _))

variable {V : Type} {v₀ : V}

/-- The completed reads that read from write `m`, in invocation order. -/
def swmrReads (α : List (Label P (register V v₀))) (w : P) (rf : OpId P → ℕ) (m : ℕ) :
    List (OpId P × RWOp V) :=
  ((invIds α).filter (fun x => decide (x.1 ≠ w ∧ Completed α x ∧ rf x = m))).map
    (fun x => (x, RWOp.read))

/-- The first `j` writes, each followed by the reads that read from it (preceded by the reads
from the initial value). -/
def swmrLinAux (α : List (Label P (register V v₀))) (w : P) (ws : List (RWOp V))
    (rf : OpId P → ℕ) : ℕ → List (OpId P × RWOp V)
  | 0 => swmrReads α w rf 0
  | j + 1 => swmrLinAux α w ws rf j ++ ((w, j), ws.getD j .read) :: swmrReads α w rf (j + 1)

/-- The reads-from linearization of `α`. -/
def swmrLin (α : List (Label P (register V v₀))) (w : P) (rf : OpId P → ℕ) :
    List (OpId P × RWOp V) :=
  swmrLinAux α w (opsOf α w) rf (opsOf α w).length

/-- Hypotheses of the SWMR reads-from criterion (see the module docstring). -/
structure SWMRReadsFrom (α : List (Label P (register V v₀))) (w : P) (rf : OpId P → ℕ) : Prop where
  wellFormed : WellFormed α
  ops : ∀ p, ∀ o ∈ opsOf α p, (p = w ∧ ∃ v, o = .write v) ∨ (p ≠ w ∧ o = .read)
  write_resp : ∀ j v x, opOf α (w, j) = some (.write v) → respOf α (w, j) = some x → x = v
  read_val : ∀ x : OpId P, x.1 ≠ w → Completed α x →
    respOf α x = some (writeVal v₀ (opsOf α w) (rf x))
  not_future : ∀ x : OpId P, x.1 ≠ w → Completed α x → 0 < rf x → ¬ Precedes α x (w, rf x - 1)
  not_overwritten : ∀ x : OpId P, x.1 ≠ w → Completed α x → ¬ Precedes α (w, rf x) x
  mono : ∀ x y : OpId P, x.1 ≠ w → y.1 ≠ w → Completed α y → Precedes α x y → rf x ≤ rf y

/-- Sort key: writes `(w, i)` get `2 i + 1`, reads `x` get `2 rf(x)`. -/
def swmrKey (w : P) (rf : OpId P → ℕ) (x : OpId P) : ℕ := if x.1 = w then 2 * x.2 + 1 else 2 * rf x

/-- The strict order used to show that the linearization respects real time. -/
def swmrBefore (α : List (Label P A)) (w : P) (rf : OpId P → ℕ) (x y : OpId P) : Prop :=
  swmrKey w rf x < swmrKey w rf y ∨
    (swmrKey w rf x = swmrKey w rf y ∧ x ≠ y ∧ [x, y].Sublist (invIds α))

lemma mem_swmrReads {α : List (Label P (register V v₀))} {w : P} {rf : OpId P → ℕ} {m : ℕ}
    {y : OpId P × RWOp V} :
    y ∈ swmrReads α w rf m ↔
      ∃ x, Invoked α x ∧ x.1 ≠ w ∧ Completed α x ∧ rf x = m ∧ y = (x, .read) := by
  simp only [swmrReads, List.mem_map, List.mem_filter, decide_eq_true_eq, mem_invIds]
  constructor
  · rintro ⟨x, ⟨h0, h1, h2, h3⟩, rfl⟩; exact ⟨x, h0, h1, h2, h3, rfl⟩
  · rintro ⟨x, h0, h1, h2, h3, rfl⟩; exact ⟨x, ⟨h0, h1, h2, h3⟩, rfl⟩

lemma mem_swmrLinAux {α : List (Label P (register V v₀))} {w : P} {ws : List (RWOp V)}
    {rf : OpId P → ℕ} (j : ℕ) {y : OpId P × RWOp V} :
    y ∈ swmrLinAux α w ws rf j ↔
      (∃ i < j, y = ((w, i), ws.getD i .read)) ∨
        (∃ x, Invoked α x ∧ x.1 ≠ w ∧ Completed α x ∧ rf x ≤ j ∧ y = (x, .read)) := by
  induction j with
  | zero =>
    simp only [swmrLinAux, mem_swmrReads, Nat.not_lt_zero, false_and, exists_false, false_or,
      Nat.le_zero]
  | succ j ih =>
    simp only [swmrLinAux, List.mem_append, ih, List.mem_cons, mem_swmrReads]
    constructor
    · rintro ((⟨i, hi, rfl⟩ | ⟨x, h0, h1, h2, h3, rfl⟩) | rfl | ⟨x, h0, h1, h2, h3, rfl⟩)
      · exact Or.inl ⟨i, by omega, rfl⟩
      · exact Or.inr ⟨x, h0, h1, h2, by omega, rfl⟩
      · exact Or.inl ⟨j, by omega, rfl⟩
      · exact Or.inr ⟨x, h0, h1, h2, by omega, rfl⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨x, h0, h1, h2, h3, rfl⟩)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact Or.inl (Or.inl ⟨i, hi, rfl⟩)
        · exact Or.inr (Or.inl rfl)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h3) with h' | h'
        · exact Or.inl (Or.inr ⟨x, h0, h1, h2, by omega, rfl⟩)
        · exact Or.inr (Or.inr ⟨x, h0, h1, h2, h', rfl⟩)

lemma pairwise_swmrReads (α : List (Label P (register V v₀))) (w : P) (rf : OpId P → ℕ)
    (m : ℕ) : (swmrReads α w rf m).Pairwise (fun y z => swmrBefore α w rf y.1 z.1) := by
  unfold swmrReads
  rw [List.pairwise_map]
  have hnd := (nodup_invIds α).filter
    (fun x => decide (x.1 ≠ w ∧ Completed α x ∧ rf x = m))
  refine (((pairwise_sublist_self (invIds α)).sublist List.filter_sublist).and hnd).imp_of_mem ?_
  intro a b ha hb hab
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  right
  refine ⟨?_, hab.2, hab.1⟩
  simp only [swmrKey, ha.2.1, hb.2.1, ite_false, ha.2.2.2, hb.2.2.2]

lemma pairwise_swmrLinAux (α : List (Label P (register V v₀))) (w : P) (ws : List (RWOp V))
    (rf : OpId P → ℕ) (j : ℕ) :
    (swmrLinAux α w ws rf j).Pairwise (fun y z => swmrBefore α w rf y.1 z.1) := by
  induction j with
  | zero => exact pairwise_swmrReads α w rf 0
  | succ j ih =>
    simp only [swmrLinAux]
    rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨ih, ⟨?_, pairwise_swmrReads α w rf _⟩, ?_⟩
    · intro z hz
      obtain ⟨x, -, hx, -, hk, rfl⟩ := mem_swmrReads.1 hz
      left
      simp only [swmrKey, hx, ite_true, ite_false, hk]
      omega
    · intro y hy z hz
      have hy' := (mem_swmrLinAux j).1 hy
      left
      rcases List.mem_cons.1 hz with rfl | hz
      · rcases hy' with ⟨i, hi, rfl⟩ | ⟨x, -, hx, -, hk, rfl⟩
        · simp only [swmrKey, ite_true]; omega
        · simp only [swmrKey, hx, ite_true, ite_false]; omega
      · obtain ⟨x', -, hx', -, hk', rfl⟩ := mem_swmrReads.1 hz
        rcases hy' with ⟨i, hi, rfl⟩ | ⟨x, -, hx, -, hk, rfl⟩
        · simp only [swmrKey, hx', ite_true, ite_false, hk']; omega
        · simp only [swmrKey, hx, hx', ite_false, hk']; omega

/-- State reached by the first `j` writes of the reads-from linearization. -/
lemma runOps_swmrLinAux (α : List (Label P (register V v₀))) (w : P) (ws : List (RWOp V))
    (rf : OpId P → ℕ) (j : ℕ) :
    (register V v₀).runOps v₀ ((swmrLinAux α w ws rf j).map Prod.snd) = writeVal v₀ ws j := by
  have hreads : ∀ m q,
      (register V v₀).runOps q ((swmrReads α w rf m).map Prod.snd) = q :=
    fun m q => ObjSpec.runOps_of_readOnly _ _ _ (by
      intro o ho
      simp only [swmrReads, List.map_map, List.mem_map] at ho
      obtain ⟨_, _, rfl⟩ := ho
      intro q; rfl)
  induction j with
  | zero => simp [swmrLinAux, hreads]
  | succ j ih =>
    rw [swmrLinAux, List.map_append, ObjSpec.runOps_append, ih, List.map_cons,
      ObjSpec.runOps_cons, hreads, writeVal_succ']

lemma seqOK_swmrReads {α : List (Label P (register V v₀))} {w : P} {rf : OpId P → ℕ} {m : ℕ}
    {q : V} (h : ∀ x, x.1 ≠ w → Completed α x → rf x = m → respOf α x = some q) :
    SeqOK α q (swmrReads α w rf m) := by
  unfold swmrReads
  generalize hl : (invIds α).filter (fun x => decide (x.1 ≠ w ∧ Completed α x ∧ rf x = m)) = l
  have hl' : ∀ x ∈ l, x.1 ≠ w ∧ Completed α x ∧ rf x = m := by
    intro x hx; rw [← hl] at hx; simpa using (List.mem_filter.1 hx).2
  clear hl
  induction l with
  | nil => trivial
  | cons x l ih =>
    refine ⟨?_, ih (fun x' hx' => hl' x' (by simp [hx']))⟩
    intro r hr
    obtain ⟨h1, h2, h3⟩ := hl' x (by simp)
    rw [h x h1 h2 h3] at hr; cases hr; rfl

/-- **Reads-from criterion for SWMR registers.** -/
theorem SWMRReadsFrom.isLinearization {α : List (Label P (register V v₀))} {w : P}
    {rf : OpId P → ℕ} (h : SWMRReadsFrom α w rf) : IsLinearization α (swmrLin α w rf) := by
  have hα := h.wellFormed
  have hL : swmrLin α w rf = swmrLinAux α w (opsOf α w) rf (opsOf α w).length := rfl
  rw [hL]
  set ws := opsOf α w with hws
  -- reads read from invoked writes
  have hrf_le : ∀ x : OpId P, x.1 ≠ w → Completed α x → rf x ≤ ws.length := by
    intro x hx hc
    by_contra hcon
    apply h.not_future x hx hc (by omega)
    exact ⟨α, [], by simp, hc, by simp only [Invoked, ← hws]; omega⟩
  have hread : ∀ x : OpId P, Invoked α x → x.1 ≠ w → opOf α x = some .read := by
    intro x hx hxw
    rcases h.ops x.1 _ (List.getElem_mem hx) with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 hxw
    · simp [opOf, List.getElem?_eq_getElem hx, h2]
  have hmem := fun y => mem_swmrLinAux (α := α) (w := w) (ws := ws) (rf := rf)
    ws.length (y := y)
  have hpw := pairwise_swmrLinAux α w ws rf ws.length
  have hcomplete : ∀ a, Completed α a →
      a ∈ (swmrLinAux α w ws rf ws.length).map Prod.fst := by
    rintro ⟨p, k⟩ ha
    have hinv := hα.invoked_of_completed ha
    by_cases hp : p = w
    · subst hp
      exact List.mem_map.2 ⟨((p, k), ws.getD k .read), (hmem _).2 (Or.inl ⟨k, hinv, rfl⟩), rfl⟩
    · exact List.mem_map.2 ⟨((p, k), .read),
        (hmem _).2 (Or.inr ⟨(p, k), hinv, hp, ha, hrf_le _ hp ha, rfl⟩), rfl⟩
  refine ⟨?_, ?_, hcomplete, ?_, ?_⟩
  · -- nodup
    refine (List.pairwise_map.2 hpw).imp ?_
    intro x y hxy heq; subst heq
    rcases hxy with hxy | ⟨-, hne, -⟩
    · exact lt_irrefl _ hxy
    · exact hne rfl
  · -- operations
    intro y hy
    rcases (hmem y).1 hy with ⟨i, hi, rfl⟩ | ⟨x, h0, hx, -, -, rfl⟩
    · simp [opOf, ← hws, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    · exact hread x h0 hx
  · -- real time
    intro a b hab hb
    have ha := hcomplete a hab.completed
    have hainv := hα.invoked_of_completed hab.completed
    have hbefore : swmrBefore α w rf a b := by
      obtain ⟨yb, hyb, rfl⟩ := List.mem_map.1 hb
      obtain ⟨p, i⟩ := a
      rcases (hmem yb).1 hyb with ⟨j, hj, rfl⟩ | ⟨x, h0, hx, hxc, -, rfl⟩
      · -- b is the write (w, j)
        left
        simp only at hab ⊢
        by_cases hp : p = w
        · subst hp
          have := Precedes.lt_of_proc hα hab
          simp only [swmrKey, ite_true]; omega
        · -- a is a read
          have hk : Completed α (p, i) := hab.completed
          have : rf (p, i) ≤ j := by
            by_contra hc
            rcases Nat.lt_or_ge j (rf (p, i) - 1) with hlt | hge
            · apply h.not_future (p, i) hp hk (by omega)
              refine Precedes.trans hα hab (hα.precedes_of_lt hlt ?_)
              have := hrf_le _ hp hk; simp only [Invoked, ← hws]; omega
            · have : j = rf (p, i) - 1 := by omega
              subst this
              exact h.not_future (p, i) hp hk (by omega) hab
          simp only [swmrKey, hp, ite_true, ite_false]; omega
      · -- b is the read x
        by_cases hp : p = w
        · -- a is the write (w, i)
          subst hp
          left
          have : i < rf x := by
            by_contra hc
            rcases Nat.lt_or_ge (rf x) i with hlt | hge
            · exact h.not_overwritten x hx hxc
                (Precedes.trans hα (hα.precedes_of_lt hlt hainv) hab)
            · have : i = rf x := by omega
              subst this
              exact h.not_overwritten x hx hxc hab
          simp only [swmrKey, hx, ite_true, ite_false]; omega
        · have hm := h.mono (p, i) x hp hx hxc hab
          have hsub := hab.sublist_invIds h0 hα
          rcases Nat.lt_or_ge (rf (p, i)) (rf x) with hlt | hge
          · left; simp only [swmrKey, hp, hx, ite_false]; omega
          · right
            refine ⟨by simp only [swmrKey, hp, hx, ite_false]; omega, ?_, hsub⟩
            rintro rfl
            exact (List.nodup_cons.1 ((nodup_invIds α).sublist hsub)).1 (by simp)
    refine sublist_pair_of_pairwise (List.pairwise_map.2 hpw) ha hb hbefore ?_
    intro h'
    rcases hbefore with h1 | ⟨h1, -, h2⟩ <;> rcases h' with h3 | ⟨h3, -, h4⟩
    · omega
    · omega
    · omega
    · exact not_sublist_pair_both (nodup_invIds α) h2 h4
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
      · exact absurd rfl h1
    have hreads : ∀ m, SeqOK α (writeVal v₀ ws m) (swmrReads α w rf m) := by
      intro m
      apply seqOK_swmrReads
      intro x hx hc hxm
      rw [h.read_val x hx hc, hxm]
    suffices ∀ j, SeqOK α v₀ (swmrLinAux α w ws rf j) from this _
    intro j
    induction j with
    | zero => exact hreads 0
    | succ j ih =>
      rw [swmrLinAux, seqOK_append, runOps_swmrLinAux]
      refine ⟨ih, hwrite j, ?_⟩
      rw [← writeVal_succ']
      exact hreads (j + 1)

/-- The final state of the reads-from linearization is the value of the last invoked write. -/
theorem linState_swmrLin (α : List (Label P (register V v₀))) (w : P) (rf : OpId P → ℕ) :
    linState (A := register V v₀) (swmrLin α w rf) =
      writeVal v₀ (opsOf α w) (opsOf α w).length :=
  runOps_swmrLinAux _ _ _ _ _

end Cslib.SharedMemory
