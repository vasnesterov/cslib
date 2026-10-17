/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Indist

/-!
# Covering arguments: poised processes, block writes, indistinguishability

Burns–Lynch style covering arguments: a process *covers* a base object when its next step blindly
overwrites it (the new state and the response do not depend on the old state, e.g. a register
write). A *block write* by processes covering the objects of a set `R` obliterates the contents of
`R`: whatever happened to `R` before, after the block write the memory only depends on the local
states of the writers and on the objects outside `R`.

## Main definitions

* `ObjSpec.Overwrites S o`: `o` is a blind write (`δ s o` independent of `s`).
* `Impl.Covers C p i`: `p` is pending and poised to overwrite base object `i`.
* `Impl.AgreeOn Q C D`: same memory and same local states / pending operations of all `q ∈ Q`
  (generalizes `Impl.Agree` to sets of processes).
* `Impl.blockWrite ps`: one step of each process in `ps`.

## Main results

* `Impl.runFrom_agreeOn`: executions of processes in `Q` cannot distinguish `Q`-agreeing
  configurations.
* `Impl.blockWrite_agreeOn`: **indistinguishability after a block write** — if `C` and `D` agree on
  the writers (and on any set `Q ⊇ ps`) and on the memory outside the covered objects, then after
  the block write they agree on `Q` and on the whole memory.
* `Impl.blockWrite_run`: a block write is enabled, only touches the covered objects and does not
  change other processes.
* `Impl.step_local`: a step only depends on the stepping process and the object it accesses.
* `Impl.exists_solo_until`: running a process solo, obstruction-freedom gives a first point at which
  it has returned or its next action has a given property (e.g. "writes outside `R`").
* `Impl.iterate_soloStep_mem_of_readOnly`, `Impl.iterate_soloStep_other`: what a solo run does not
  change.

## Agreement, poised processes and commuting steps

* `Impl.AgreeOn Q` is an equivalence relation (`AgreeOn.refl`, `AgreeOn.symm`, `AgreeOn.trans`),
  and agreement on all processes is equality (`AgreeOn.univ_eq`).
* `Impl.PoisedAt I C p i o`: `p` is pending in `C` and its next step applies `o` to the base
  object `i`; `Covers` is `PoisedAt` with a blind overwrite (`covers_iff_poisedAt`). Both only
  depend on the local state and pending operation of the process (`PoisedAt.congr`,
  `Covers.congr`), and a process is poised at, and covers, at most one base object
  (`PoisedAt.unique`, `Covers.unique`).
* Block writes: `opsOf_blockWrite`, `respsOf_blockWrite`, `blockWrite_append`,
  `runFrom_blockWrite_other`; `applyAccesses M as`: the memory `M` after the accesses `as` (base
  object and operation), applied in order; `Impl.runFrom_poised_block`: distinct poised processes
  take one step each; `Impl.blockWrite_swap`: two block writes by covering processes to the same
  set of objects commute, up to the memory inside that set.
* `Impl.mem_of_step`: a step changes at most the base object accessed by an internal step;
  `Impl.step_exact`: exact version of `step_local`; `Impl.step_comm`: steps of distinct processes
  commute unless both access the same base object and one of them changes it.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace Cslib.SharedMemory

/-- `o` is a *blind write* (an overwrite): its resulting state and its response do not depend on
the state it is applied to. -/
def ObjSpec.Overwrites (S : ObjSpec) (o : S.Op) : Prop := ∀ s s', S.δ s o = S.δ s' o

lemma register_write_overwrites {V : Type} (v₀ v : V) :
    (register V v₀).Overwrites (.write v) := fun _ _ => rfl

lemma register_read_readOnly {V : Type} (v₀ : V) : (register V v₀).ReadOnly .read :=
  fun _ => rfl

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-- In configuration `C`, process `p` *covers* base object `i`: it is pending and its next step
blindly overwrites `i`. -/
def Covers (C : Config A B P L) (p : P) (i : ι) : Prop :=
  C.pend p ≠ none ∧ ∃ o k, I.act p (C.loc p) = .access i o k ∧ (B i).Overwrites o

/-- `C` and `D` have the same memory and agree on every process of `Q`. -/
structure AgreeOn (Q : Set P) (C D : Config A B P L) : Prop where
  mem : C.mem = D.mem
  loc : ∀ q ∈ Q, C.loc q = D.loc q
  pend : ∀ q ∈ Q, C.pend q = D.pend q

omit [DecidableEq P] [DecidableEq ι] in
lemma AgreeOn.symm {Q : Set P} {C D : Config A B P L} (h : AgreeOn Q C D) : AgreeOn Q D C :=
  ⟨h.mem.symm, fun q hq => (h.loc q hq).symm, fun q hq => (h.pend q hq).symm⟩

omit [DecidableEq P] [DecidableEq ι] in
lemma AgreeOn.agree {Q : Set P} {C D : Config A B P L} (h : AgreeOn Q C D) {p : P} (hp : p ∈ Q) :
    Agree p C D := ⟨h.mem, h.loc p hp, h.pend p hp⟩

omit [DecidableEq P] [DecidableEq ι] in
lemma AgreeOn.mono {Q Q' : Set P} {C D : Config A B P L} (h : AgreeOn Q C D) (hQ : Q' ⊆ Q) :
    AgreeOn Q' C D := ⟨h.mem, fun q hq => h.loc q (hQ hq), fun q hq => h.pend q (hQ hq)⟩

variable {I}

/-- A step of a process of `Q` preserves `Q`-agreement. -/
lemma step_agreeOn {Q : Set P} {C D C' : Config A B P L} (h : AgreeOn Q C D) {ℓ : Label P A}
    (hℓ : ℓ.proc ∈ Q) (hC : I.step C ℓ = some C') :
    ∃ D', I.step D ℓ = some D' ∧ AgreeOn Q C' D' := by
  obtain ⟨D', hD', hag⟩ := step_agree (h.agree hℓ) rfl hC
  refine ⟨D', hD', hag.mem, fun q hq => ?_, fun q hq => ?_⟩
  · by_cases hqp : q = ℓ.proc
    · subst hqp; exact hag.loc
    · rw [(step_other hC (Ne.symm hqp)).1, (step_other hD' (Ne.symm hqp)).1, h.loc q hq]
  · by_cases hqp : q = ℓ.proc
    · subst hqp; exact hag.pend
    · rw [(step_other hC (Ne.symm hqp)).2, (step_other hD' (Ne.symm hqp)).2, h.pend q hq]

/-- Executions of processes of `Q` cannot distinguish `Q`-agreeing configurations. -/
lemma runFrom_agreeOn {Q : Set P} {C D C' : Config A B P L} (h : AgreeOn Q C D)
    {β : List (Label P A)} (hβ : ∀ ℓ ∈ β, ℓ.proc ∈ Q) (hC : I.runFrom C β = some C') :
    ∃ D', I.runFrom D β = some D' ∧ AgreeOn Q C' D' := by
  induction β generalizing C D with
  | nil =>
    simp only [runFrom_nil, Option.some.injEq] at hC; subst hC; exact ⟨D, rfl, h⟩
  | cons ℓ β ih =>
    simp only [runFrom_cons] at hC
    cases hs : I.step C ℓ with
    | none => simp [hs] at hC
    | some C₁ =>
      simp only [hs, Option.bind_some] at hC
      obtain ⟨D₁, hD₁, h₁⟩ := step_agreeOn h (hβ ℓ (by simp)) hs
      obtain ⟨D', hD', h'⟩ := ih h₁ (fun ℓ' hℓ' => hβ ℓ' (by simp [hℓ'])) hC
      exact ⟨D', by simp [hD₁, hD'], h'⟩

/-- **Locality of steps.** A step of `p` only depends on the local state and pending operation of
`p` and on the object it accesses — and not even on that object if the access is a blind write.
Afterwards the two configurations agree on `p`, and every object either is unchanged on both
sides or has the same state on both sides. -/
lemma step_local {p : P} {C D C' : Config A B P L} (hloc : C.loc p = D.loc p)
    (hpend : C.pend p = D.pend p)
    {ℓ : Label P A} (hℓ : ℓ.proc = p)
    (hmem : ℓ = .tau p → ∀ i o k, I.act p (C.loc p) = .access i o k → ¬ (B i).Overwrites o →
      C.mem i = D.mem i)
    (hC : I.step C ℓ = some C') :
    ∃ D', I.step D ℓ = some D' ∧ C'.loc p = D'.loc p ∧ C'.pend p = D'.pend p ∧
      ∀ j, (C'.mem j = C.mem j ∧ D'.mem j = D.mem j) ∨ C'.mem j = D'.mem j := by
  classical
  cases ℓ with
  | inv q o =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨h0, h1, h2, h3, h4⟩ := step_inv hC
    refine ⟨{ D with pend := Function.update D.pend q (some o),
                     loc := Function.update D.loc q (I.invoke q (D.loc q) o) },
      by simp [step, ← hpend, h0, h1], by rw [h3]; simp [hloc], by rw [h2]; simp,
      fun j => Or.inl ⟨by rw [h4], rfl⟩⟩
  | tau q =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨h0, h1, i, o, k, hact, hm, hl⟩ := step_tau hC
    have hact' : I.act q (D.loc q) = .access i o k := by rw [← hloc, hact]
    have hδ : (B i).δ (C.mem i) o = (B i).δ (D.mem i) o := by
      by_cases hov : (B i).Overwrites o
      · exact hov _ _
      · rw [hmem rfl i o k hact hov]
    refine ⟨{ D with mem := Function.update D.mem i ((B i).δ (D.mem i) o).1,
                     loc := Function.update D.loc q (k ((B i).δ (D.mem i) o).2) },
      by simp [step, ← hpend, h0, hact'], by rw [hl]; simp [hδ], by rw [h1]; exact hpend,
      fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; right; rw [hm]; simp [hδ]
    · left; rw [hm]; simp [Function.update_of_ne hj]
  | ret q r =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨h0, h1, h2, l, hact, hl⟩ := step_ret hC
    have hact' : I.act q (D.loc q) = .ret r l := by rw [← hloc, hact]
    refine ⟨{ D with pend := Function.update D.pend q none, loc := Function.update D.loc q l },
      by simp [step, ← hpend, h0, hact'], by rw [hl]; simp, by rw [h1]; simp,
      fun j => Or.inl ⟨by rw [h2], rfl⟩⟩

/-! ### Block writes -/

omit [DecidableEq P] [DecidableEq ι] in
variable (I) in
/-- A block write: one step by each process of `ps`, in order. -/
def blockWrite (ps : List P) : List (Label P A) := ps.map Label.tau

omit [DecidableEq P] [DecidableEq ι] in
@[simp] lemma blockWrite_nil : blockWrite (A := A) ([] : List P) = [] := rfl

omit [DecidableEq P] [DecidableEq ι] in
@[simp] lemma blockWrite_cons (p : P) (ps : List P) :
    blockWrite (A := A) (p :: ps) = .tau p :: blockWrite ps := rfl

omit [DecidableEq P] [DecidableEq ι] in
lemma mem_blockWrite {ps : List P} {ℓ : Label P A} (h : ℓ ∈ blockWrite ps) : ℓ.proc ∈ ps := by
  simp only [blockWrite, List.mem_map] at h
  obtain ⟨p, hp, rfl⟩ := h; exact hp

/-- The step of a covering process. -/
lemma step_of_covers {C : Config A B P L} {p : P} {i : ι} (h : I.Covers C p i) :
    ∃ o k, I.act p (C.loc p) = .access i o k ∧ (B i).Overwrites o ∧
      I.step C (.tau p) = some { C with
        mem := Function.update C.mem i ((B i).δ (C.mem i) o).1,
        loc := Function.update C.loc p (k ((B i).δ (C.mem i) o).2) } := by
  obtain ⟨hp, o, k, hact, hov⟩ := h
  exact ⟨o, k, hact, hov, by simp [step, hp, hact]⟩

/-- **Indistinguishability after a block write.** Let the distinct processes `c.1` cover the
objects `c.2`, `c ∈ cs`, in `C`, and let `D` agree with `C` on all processes of a set `Q`
containing the writers and on the memory outside the covered objects. Then after the block write,
`C` and `D` agree on `Q` and on the whole memory: the block write has obliterated every difference
inside the covered objects. -/
theorem blockWrite_agreeOn {Q : Set P} {cs : List (P × ι)} (hnd : (cs.map Prod.fst).Nodup)
    (hQ : ∀ c ∈ cs, c.1 ∈ Q) {C D : Config A B P L} (hcov : ∀ c ∈ cs, I.Covers C c.1 c.2)
    (hloc : ∀ q ∈ Q, C.loc q = D.loc q) (hpend : ∀ q ∈ Q, C.pend q = D.pend q)
    (hmem : ∀ i, i ∉ cs.map Prod.snd → C.mem i = D.mem i) :
    ∃ C' D', I.runFrom C (blockWrite (cs.map Prod.fst)) = some C' ∧
      I.runFrom D (blockWrite (cs.map Prod.fst)) = some D' ∧ AgreeOn Q C' D' := by
  induction cs generalizing C D with
  | nil =>
    refine ⟨C, D, rfl, rfl, funext fun i => hmem i (by simp), hloc, hpend⟩
  | cons c cs ih =>
    obtain ⟨p, j⟩ := c
    have hpQ : p ∈ Q := hQ (p, j) (by simp)
    obtain ⟨o, k, hact, hov, hC⟩ := step_of_covers (hcov (p, j) (by simp))
    have hcovD : I.Covers D p j :=
      ⟨by rw [← hpend p hpQ]; exact (hcov (p, j) (by simp)).1, o, k, by rw [← hloc p hpQ, hact],
        hov⟩
    obtain ⟨o', k', hact', -, hD⟩ := step_of_covers hcovD
    rw [← hloc p hpQ, hact] at hact'
    simp only [Action.access.injEq, heq_eq_eq, true_and] at hact'
    obtain ⟨rfl, rfl⟩ := hact'
    have hp_notin : p ∉ cs.map Prod.fst := (List.nodup_cons.1 hnd).1
    set C₁ : Config A B P L := { C with
        mem := Function.update C.mem j ((B j).δ (C.mem j) o).1,
        loc := Function.update C.loc p (k ((B j).δ (C.mem j) o).2) } with hC₁
    set D₁ : Config A B P L := { D with
        mem := Function.update D.mem j ((B j).δ (D.mem j) o).1,
        loc := Function.update D.loc p (k ((B j).δ (D.mem j) o).2) } with hD₁
    have hδ := hov (C.mem j) (D.mem j)
    obtain ⟨C', D', h1, h2, h3⟩ := ih (C := C₁) (D := D₁) (List.nodup_cons.1 hnd).2
      (fun c hc => hQ c (by simp [hc]))
      (fun c hc => by
        have hqp : c.1 ≠ p := fun h => hp_notin (h ▸ List.mem_map_of_mem hc)
        obtain ⟨hq1, o₂, k₂, h₂, hov₂⟩ := hcov c (by simp [hc])
        exact ⟨by simpa [hC₁] using hq1, o₂, k₂, by simpa [hC₁, hqp] using h₂, hov₂⟩)
      (fun q hq => by
        by_cases hqp : q = p
        · subst hqp; simp [hC₁, hD₁, hδ]
        · simp [hC₁, hD₁, hqp, hloc q hq])
      (fun q hq => by simpa [hC₁, hD₁] using hpend q hq)
      (fun i hi => by
        by_cases hip : i = j
        · subst hip; simp [hC₁, hD₁, hδ]
        · simp only [hC₁, hD₁, Function.update_of_ne hip]
          exact hmem i (by simp [hip, hi]))
    refine ⟨C', D', ?_, ?_, h3⟩
    · simp [hC, h1]
    · simp [hD, h2]

/-- A block write by distinct covering processes is enabled, changes only the covered objects and
does not change the other processes. -/
theorem blockWrite_run {cs : List (P × ι)} (hnd : (cs.map Prod.fst).Nodup) {C : Config A B P L}
    (hcov : ∀ c ∈ cs, I.Covers C c.1 c.2) :
    ∃ C', I.runFrom C (blockWrite (cs.map Prod.fst)) = some C' ∧
      (∀ q, q ∉ cs.map Prod.fst → C'.loc q = C.loc q ∧ C'.pend q = C.pend q) ∧
      (∀ i, i ∉ cs.map Prod.snd → C'.mem i = C.mem i) := by
  induction cs generalizing C with
  | nil => exact ⟨C, rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩
  | cons c cs ih =>
    obtain ⟨p, j⟩ := c
    obtain ⟨o, k, hact, hov, hC⟩ := step_of_covers (hcov (p, j) (by simp))
    have hp_notin : p ∉ cs.map Prod.fst := (List.nodup_cons.1 hnd).1
    set C₁ : Config A B P L := { C with
        mem := Function.update C.mem j ((B j).δ (C.mem j) o).1,
        loc := Function.update C.loc p (k ((B j).δ (C.mem j) o).2) } with hC₁
    obtain ⟨C', h1, h2, h3⟩ := ih (C := C₁) (List.nodup_cons.1 hnd).2 (fun c hc => by
        have hqp : c.1 ≠ p := fun h => hp_notin (h ▸ List.mem_map_of_mem hc)
        obtain ⟨hq1, o₂, k₂, h₂, hov₂⟩ := hcov c (by simp [hc])
        exact ⟨by simpa [hC₁] using hq1, o₂, k₂, by simpa [hC₁, hqp] using h₂, hov₂⟩)
    refine ⟨C', by simp [hC, h1], fun q hq => ?_, fun i hi => ?_⟩
    · have hqp : q ≠ p := fun h => hq (by simp [h])
      rw [(h2 q (fun h => hq (by simp [h]))).1, (h2 q (fun h => hq (by simp [h]))).2]
      simp [hC₁, hqp]
    · have hip : i ≠ j := fun h => hi (by simp [h])
      rw [h3 i (fun h => hi (by simp [h]))]
      simp [hC₁, hip]

/-- Internal steps do not change pending operations. -/
lemma runFrom_pend_of_tau {C C' : Config A B P L} {β : List (Label P A)}
    (h : I.runFrom C β = some C') (hβ : ∀ ℓ ∈ β, ∃ p, ℓ = .tau p) : C'.pend = C.pend := by
  induction β generalizing C with
  | nil => simp only [runFrom_nil, Option.some.injEq] at h; subst h; rfl
  | cons ℓ β ih =>
    simp only [runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨p, rfl⟩ := hβ ℓ (by simp)
      rw [ih h (fun ℓ' hℓ' => hβ ℓ' (by simp [hℓ'])), (step_tau hs).2.1]

omit [DecidableEq P] in
lemma blockWrite_tau {ps : List P} : ∀ ℓ ∈ (blockWrite ps : List (Label P A)), ∃ p, ℓ = .tau p := by
  intro ℓ hℓ
  simp only [blockWrite, List.mem_map] at hℓ
  obtain ⟨p, -, rfl⟩ := hℓ; exact ⟨p, rfl⟩

/-! ### Solo runs -/

variable (I) in
/-- Running `p` solo from `C` until it returns, there is a first point at which `p` has returned
or its next action satisfies `Q`; before it, `p` stays pending and its actions violate `Q`. -/
lemma exists_solo_until (p : P) (C : Config A B P L) (Q : Action A B L → Prop)
    (hfin : ∃ K, ((I.soloStep p)^[K] C).pend p = none) :
    ∃ m, (∀ j < m, ((I.soloStep p)^[j] C).pend p ≠ none ∧
        ¬ Q (I.act p (((I.soloStep p)^[j] C).loc p))) ∧
      (((I.soloStep p)^[m] C).pend p = none ∨ Q (I.act p (((I.soloStep p)^[m] C).loc p))) := by
  classical
  have hex : ∃ m, ((I.soloStep p)^[m] C).pend p = none ∨
      Q (I.act p (((I.soloStep p)^[m] C).loc p)) := by
    obtain ⟨K, hK⟩ := hfin; exact ⟨K, Or.inl hK⟩
  refine ⟨Nat.find hex, fun j hj => ?_, Nat.find_spec hex⟩
  have := Nat.find_min hex hj
  push Not at this
  exact this

lemma soloStep_other {p q : P} (hq : q ≠ p) (C : Config A B P L) :
    (I.soloStep p C).loc q = C.loc q ∧ (I.soloStep p C).pend q = C.pend q := by
  unfold soloStep
  split_ifs with h
  · exact ⟨rfl, rfl⟩
  · obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 (I.step_nextLabel_isSome C p h)
    rw [hC', Option.getD_some]
    exact step_other hC' (by rw [I.nextLabel_proc]; exact Ne.symm hq)

lemma iterate_soloStep_other {p q : P} (hq : q ≠ p) (C : Config A B P L) (m : ℕ) :
    ((I.soloStep p)^[m] C).loc q = C.loc q ∧ ((I.soloStep p)^[m] C).pend q = C.pend q := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    rw [(soloStep_other hq _).1, (soloStep_other hq _).2, ih.1, ih.2]; exact ⟨rfl, rfl⟩

/-- One solo step of `p` changes the memory only at the object `p` accesses, and not at all if
the access is read-only. -/
lemma soloStep_mem (p : P) (C : Config A B P L) (i : ι)
    (h : ∀ o k, I.act p (C.loc p) = .access i o k → (B i).ReadOnly o) :
    (I.soloStep p C).mem i = C.mem i := by
  unfold soloStep
  split_ifs with hp
  · rfl
  · obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 (I.step_nextLabel_isSome C p hp)
    rw [hC', Option.getD_some]
    unfold nextLabel at hC'
    split at hC'
    · rename_i j o k hact
      obtain ⟨-, -, j', o', k', hact', hm, -⟩ := step_tau hC'
      rw [hact] at hact'
      simp only [Action.access.injEq] at hact'
      obtain ⟨rfl, hoo, hkk⟩ := hact'
      rw [hm]
      by_cases hij : i = j
      · subst hij
        have hoo' : o = o' := eq_of_heq hoo
        subst hoo'
        simp only [Function.update_self]
        exact h o k hact (C.mem i)
      · simp [Function.update_of_ne hij]
    · rw [(step_ret hC').2.2.1]

/-- If, during `m` solo steps, every access of `p` to an object outside `R` is read-only, the
memory outside `R` is unchanged. -/
lemma iterate_soloStep_mem_of_readOnly (p : P) (C : Config A B P L) (R : Set ι) (m : ℕ)
    (h : ∀ j < m, ∀ i o k, I.act p (((I.soloStep p)^[j] C).loc p) = .access i o k → i ∉ R →
      (B i).ReadOnly o) :
    ∀ i ∉ R, ((I.soloStep p)^[m] C).mem i = C.mem i := by
  induction m with
  | zero => intro i _; rfl
  | succ m ih =>
    intro i hi
    rw [Function.iterate_succ_apply', soloStep_mem p _ i
      (fun o k hact => h m (by omega) i o k hact hi)]
    exact ih (fun j hj => h j (by omega)) i hi

end Impl

end Cslib.SharedMemory

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

/-! ### Agreement of configurations -/

/-- Agreement is reflexive. -/
@[refl] lemma AgreeOn.refl (Q : Set P) (C : Config A B P L) : AgreeOn Q C C :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Agreement is transitive. -/
lemma AgreeOn.trans {Q : Set P} {C D E : Config A B P L} (h₁ : AgreeOn Q C D)
    (h₂ : AgreeOn Q D E) : AgreeOn Q C E :=
  ⟨h₁.mem.trans h₂.mem, fun q hq => (h₁.loc q hq).trans (h₂.loc q hq),
    fun q hq => (h₁.pend q hq).trans (h₂.pend q hq)⟩

/-- Configurations that agree on all processes are equal. -/
lemma AgreeOn.univ_eq {C D : Config A B P L} (h : AgreeOn Set.univ C D) : C = D := by
  cases C; cases D
  simp only [Config.mk.injEq]
  exact ⟨funext fun q => h.loc q trivial, funext fun q => h.pend q trivial, h.mem⟩

/-- Agreement on all processes is equality. -/
lemma agreeOn_univ_iff {C D : Config A B P L} : AgreeOn Set.univ C D ↔ C = D :=
  ⟨AgreeOn.univ_eq, fun h => h ▸ AgreeOn.refl _ _⟩

/-! ### Poised and covering processes -/

variable (I : Impl A B P L)

/-- In `C`, process `p` is *poised* to apply `o` to base object `i`: it is pending and its next
step is this access. -/
def PoisedAt (C : Config A B P L) (p : P) (i : ι) (o : (B i).Op) : Prop :=
  C.pend p ≠ none ∧ ∃ k, I.act p (C.loc p) = .access i o k

variable {I}

/-- Covering is being poised to apply a blind overwrite. -/
lemma covers_iff_poisedAt {C : Config A B P L} {p : P} {i : ι} :
    I.Covers C p i ↔ ∃ o, I.PoisedAt C p i o ∧ (B i).Overwrites o :=
  ⟨fun ⟨hp, o, k, hk, ho⟩ => ⟨o, ⟨hp, k, hk⟩, ho⟩, fun ⟨o, ⟨hp, k, hk⟩, ho⟩ => ⟨hp, o, k, hk, ho⟩⟩

/-- Being poised only depends on the local state and the pending operation. -/
lemma PoisedAt.congr {C D : Config A B P L} {p : P} {i : ι} {o : (B i).Op}
    (h : I.PoisedAt C p i o) (hl : C.loc p = D.loc p) (hp : C.pend p = D.pend p) :
    I.PoisedAt D p i o :=
  ⟨hp ▸ h.1, hl ▸ h.2⟩

/-- Covering only depends on the local state and the pending operation. -/
lemma Covers.congr {C D : Config A B P L} {p : P} {i : ι} (h : I.Covers C p i)
    (hl : C.loc p = D.loc p) (hp : C.pend p = D.pend p) : I.Covers D p i := by
  obtain ⟨h1, o, k, h2, h3⟩ := h
  exact ⟨hp ▸ h1, o, k, hl ▸ h2, h3⟩

/-- A process is poised at most at one base object. -/
lemma PoisedAt.unique {C : Config A B P L} {p : P} {i j : ι} {o : (B i).Op} {o' : (B j).Op}
    (hi : I.PoisedAt C p i o) (hj : I.PoisedAt C p j o') : i = j := by
  obtain ⟨-, k, h1⟩ := hi
  obtain ⟨-, k', h2⟩ := hj
  rw [h1] at h2
  cases h2; rfl

/-- A process covers at most one base object. -/
lemma Covers.unique {C : Config A B P L} {p : P} {i j : ι} (hi : I.Covers C p i)
    (hj : I.Covers C p j) : i = j := by
  obtain ⟨o, hi, -⟩ := covers_iff_poisedAt.1 hi
  obtain ⟨o', hj, -⟩ := covers_iff_poisedAt.1 hj
  exact hi.unique hj

/-! ### Block writes -/

variable [DecidableEq P]

/-- A block write invokes nothing. -/
@[simp] lemma opsOf_blockWrite (ps : List P) (q : P) :
    opsOf (blockWrite (A := A) ps) q = [] := by
  simp [opsOf, blockWrite, List.filterMap_map, Function.comp_def]

/-- A block write returns nothing. -/
@[simp] lemma respsOf_blockWrite (ps : List P) (q : P) :
    respsOf (blockWrite (A := A) ps) q = [] := by
  simp [respsOf, blockWrite, List.filterMap_map, Function.comp_def]

omit [DecidableEq P] in
/-- Block writes of concatenated lists of processes. -/
@[simp] lemma blockWrite_append (ps qs : List P) :
    blockWrite (A := A) (ps ++ qs) = blockWrite ps ++ blockWrite qs := by
  simp [blockWrite]

/-- A block write does not change the processes outside it. -/
lemma runFrom_blockWrite_other [DecidableEq ι] {C C' : Config A B P L} {ps : List P}
    (h : I.runFrom C (blockWrite ps) = some C') {q : P} (hq : q ∉ ps) :
    C'.loc q = C.loc q ∧ C'.pend q = C.pend q :=
  I.runFrom_other h fun _ hℓ he => hq (he ▸ mem_blockWrite hℓ)

end Impl

/-- The memory `M` after applying the accesses `as` (a base object and an operation on it), in
order. -/
def applyAccesses [DecidableEq ι] (M : ∀ i, (B i).State) :
    List (Σ i, (B i).Op) → ∀ i, (B i).State
  | [] => M
  | a :: as => applyAccesses (Function.update M a.1 ((B a.1).δ (M a.1) a.2).1) as

section applyAccesses

variable [DecidableEq ι]

/-- No accesses: the memory is unchanged. -/
@[simp] lemma applyAccesses_nil (M : ∀ i, (B i).State) : applyAccesses M [] = M := rfl

/-- The first access is applied first. -/
@[simp] lemma applyAccesses_cons (M : ∀ i, (B i).State) (a : Σ i, (B i).Op)
    (as : List (Σ i, (B i).Op)) :
    applyAccesses M (a :: as) =
      applyAccesses (Function.update M a.1 ((B a.1).δ (M a.1) a.2).1) as := rfl

/-- Accesses of concatenated lists are applied one list after the other. -/
lemma applyAccesses_append (M : ∀ i, (B i).State) (as bs : List (Σ i, (B i).Op)) :
    applyAccesses M (as ++ bs) = applyAccesses (applyAccesses M as) bs := by
  induction as generalizing M with
  | nil => rfl
  | cons a as ih => exact ih _

/-- Accesses to a single base object `i` apply their operations to its state, in order. -/
lemma applyAccesses_map_mk (M : ∀ i, (B i).State) (i : ι) (os : List (B i).Op) :
    applyAccesses M (os.map (Sigma.mk i)) = Function.update M i ((B i).runOps (M i) os) := by
  induction os generalizing M with
  | nil => simp
  | cons o os ih => simp [ih, ObjSpec.runOps_cons]

/-- Base objects that are not accessed keep their state. -/
lemma applyAccesses_of_forall_ne (M : ∀ i, (B i).State) {as : List (Σ i, (B i).Op)} {j : ι}
    (h : ∀ a ∈ as, a.1 ≠ j) : applyAccesses M as j = M j := by
  induction as generalizing M with
  | nil => rfl
  | cons a as ih =>
    rw [applyAccesses_cons, ih _ fun b hb => h b (List.mem_cons_of_mem _ hb),
      Function.update_of_ne (h a List.mem_cons_self).symm]

end applyAccesses

namespace Impl

variable [DecidableEq P] [DecidableEq ι] {I : Impl A B P L}

/-- **A block of poised processes.** If the distinct processes `e.1` are poised to perform the
accesses `e.2` in `C`, then they can take one step each, in order: the memory becomes
`applyAccesses C.mem`, pending operations do not change, the other processes do not move, and
each process of the block continues with the response of its access. -/
theorem runFrom_poised_block {es : List (P × Σ i, (B i).Op)} (hnd : (es.map Prod.fst).Nodup)
    {C : Config A B P L} (h : ∀ e ∈ es, I.PoisedAt C e.1 e.2.1 e.2.2) :
    ∃ C', I.runFrom C (blockWrite (es.map Prod.fst)) = some C' ∧
      C'.mem = applyAccesses C.mem (es.map Prod.snd) ∧ C'.pend = C.pend ∧
      (∀ q ∉ es.map Prod.fst, C'.loc q = C.loc q) ∧
      (∀ e ∈ es, ∃ k s, I.act e.1 (C.loc e.1) = .access e.2.1 e.2.2 k ∧
        C'.loc e.1 = k ((B e.2.1).δ s e.2.2).2) := by
  induction es generalizing C with
  | nil => exact ⟨C, rfl, rfl, rfl, fun _ _ => rfl, by simp⟩
  | cons e es ih =>
    obtain ⟨p, i, o⟩ := e
    obtain ⟨hp, k, hk⟩ := h (p, ⟨i, o⟩) List.mem_cons_self
    obtain ⟨hpes, hnd'⟩ := List.nodup_cons.1 hnd
    set C₁ : Config A B P L := { C with
      mem := Function.update C.mem i ((B i).δ (C.mem i) o).1,
      loc := Function.update C.loc p (k ((B i).δ (C.mem i) o).2) } with hC₁
    have hs : I.step C (.tau p) = some C₁ := by simp [step, hp, hk, hC₁]
    have hne : ∀ e ∈ es, e.1 ≠ p := fun e he h => hpes (List.mem_map.2 ⟨e, he, h⟩)
    obtain ⟨C', h1, h2, h3, h4, h5⟩ := ih hnd' (C := C₁) fun e he => by
      refine (h e (List.mem_cons_of_mem _ he)).congr ?_ rfl
      simp [hC₁, Function.update_of_ne (hne e he)]
    refine ⟨C', by simp [hs, h1], by simp [h2, hC₁], h3, fun q hq => ?_, fun e he => ?_⟩
    · have hqp : q ≠ p := fun e => hq (by simp [e])
      rw [h4 q fun h => hq (List.mem_cons_of_mem _ h)]
      simp [hC₁, hqp]
    · rcases List.mem_cons.1 he with rfl | he
      · refine ⟨k, C.mem i, hk, ?_⟩
        rw [h4 _ hpes]
        simp [hC₁]
      · obtain ⟨k', s, hk', hl⟩ := h5 e he
        refine ⟨k', s, ?_, hl⟩
        simpa [hC₁, Function.update_of_ne (hne e he)] using hk'

/-- **Commuting block writes.** Two block writes by distinct processes covering the same set of
base objects can be performed in either order: the results agree on all processes and on the
memory outside the covered objects. -/
lemma blockWrite_swap {C : Config A B P L} {b b' : List (P × ι)}
    (hnd : (b.map Prod.fst ++ b'.map Prod.fst).Nodup)
    (hcov : ∀ c ∈ b ++ b', I.Covers C c.1 c.2)
    (hsnd : ∀ j, j ∈ b.map Prod.snd ↔ j ∈ b'.map Prod.snd) :
    ∃ X X', I.runFrom C (blockWrite (b.map Prod.fst) ++ blockWrite (b'.map Prod.fst)) = some X ∧
      I.runFrom C (blockWrite (b'.map Prod.fst) ++ blockWrite (b.map Prod.fst)) = some X' ∧
      (∀ q, X.loc q = X'.loc q ∧ X.pend q = X'.pend q) ∧
      (∀ j, j ∉ b.map Prod.snd → X.mem j = X'.mem j) := by
  obtain ⟨hnd₁, hnd₂, hdis⟩ := List.nodup_append.1 hnd
  have hcb : ∀ c ∈ b, I.Covers C c.1 c.2 := fun c hc => hcov c (List.mem_append_left _ hc)
  have hcb' : ∀ c ∈ b', I.Covers C c.1 c.2 := fun c hc => hcov c (List.mem_append_right _ hc)
  have hn₁ : ∀ c ∈ b, c.1 ∉ b'.map Prod.fst := fun c hc h =>
    hdis _ (List.mem_map_of_mem hc) _ h rfl
  have hn₂ : ∀ c ∈ b', c.1 ∉ b.map Prod.fst := fun c hc h =>
    hdis _ h _ (List.mem_map_of_mem hc) rfl
  obtain ⟨Y, hY, hYo, hYm⟩ := blockWrite_run (I := I) hnd₁ hcb
  obtain ⟨Y', hY', hY'o, hY'm⟩ := blockWrite_run (I := I) hnd₂ hcb'
  obtain ⟨Z, X', hZ, hX', hag⟩ := blockWrite_agreeOn (I := I)
    (Q := {q | q ∉ b'.map Prod.fst}) (cs := b) hnd₁ hn₁ (C := C) (D := Y') hcb
    (fun q hq => (hY'o q hq).1.symm) (fun q hq => (hY'o q hq).2.symm)
    (fun j hj => (hY'm j (fun h => hj ((hsnd j).2 h))).symm)
  rw [hY] at hZ; cases hZ
  obtain ⟨Z', X, hZ', hX, hag'⟩ := blockWrite_agreeOn (I := I)
    (Q := {q | q ∉ b.map Prod.fst}) (cs := b') hnd₂ hn₂ (C := C) (D := Y) hcb'
    (fun q hq => (hYo q hq).1.symm) (fun q hq => (hYo q hq).2.symm)
    (fun j hj => (hYm j (fun h => hj ((hsnd j).1 h))).symm)
  rw [hY'] at hZ'; cases hZ'
  refine ⟨X, X', by rw [runFrom_append_of_eq I hY, hX], by rw [runFrom_append_of_eq I hY', hX'],
    fun q => ?_, fun j hj => ?_⟩
  · by_cases hq : q ∈ b.map Prod.fst
    · have hq' : q ∉ b'.map Prod.fst := fun h => hdis _ hq _ h rfl
      have h1 := runFrom_blockWrite_other hX hq'
      rw [h1.1, h1.2]; exact ⟨hag.loc q hq', hag.pend q hq'⟩
    · have h1 := runFrom_blockWrite_other hX' hq
      rw [h1.1, h1.2]; exact ⟨(hag'.loc q hq).symm, (hag'.pend q hq).symm⟩
  · rw [← hag'.mem, ← hag.mem, hY'm j (fun h => hj ((hsnd j).2 h)), hYm j hj]

/-! ### Locality and commutation of steps -/

/-- The memory after a step: unchanged, except for the base object accessed by an internal step
of a pending process. -/
lemma mem_of_step {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C') (j : ι) :
    C'.mem j = C.mem j ∨ (ℓ = .tau ℓ.proc ∧ C.pend ℓ.proc ≠ none ∧
      ∃ o k, I.act ℓ.proc (C.loc ℓ.proc) = .access j o k ∧
        C'.mem j = ((B j).δ (C.mem j) o).1) := by
  cases ℓ with
  | inv q o => left; rw [(step_inv h).2.2.2.2]
  | ret q r => left; rw [(step_ret h).2.2.1]
  | tau q =>
    obtain ⟨h0, -, i, o, k, hact, hm, -⟩ := step_tau h
    by_cases hj : j = i
    · subst hj; right; exact ⟨rfl, h0, o, k, hact, by simp [hm]⟩
    · left; simp [hm, Function.update_of_ne hj]

/-- **Exact locality of steps.** A step of `a` only depends on the local state and pending
operation of `a` and on the state of the object it accesses: it can be replayed in `D`, the
other processes of `D` do not move, and on every base object either both steps leave the memory
unchanged or the results agree (and the step is an access of `a` to that object). -/
lemma step_exact {a : P} {C D C' : Config A B P L} {ℓ : Label P A} (hℓ : ℓ.proc = a)
    (hloc : C.loc a = D.loc a) (hpend : C.pend a = D.pend a)
    (hobj : ∀ i o k, ℓ = .tau a → I.act a (C.loc a) = .access i o k → C.mem i = D.mem i)
    (h : I.step C ℓ = some C') :
    ∃ D', I.step D ℓ = some D' ∧ D'.loc a = C'.loc a ∧ D'.pend a = C'.pend a ∧
      (∀ q, q ≠ a → D'.loc q = D.loc q ∧ D'.pend q = D.pend q) ∧
      ∀ j, (D'.mem j = D.mem j ∧ C'.mem j = C.mem j) ∨
        (D'.mem j = C'.mem j ∧ ℓ = .tau a ∧ ∃ o k, I.act a (C.loc a) = .access j o k) := by
  obtain ⟨D', hD', hl, hp, hm⟩ :=
    step_local hloc hpend hℓ (fun hτ i o k hact _ => hobj i o k hτ hact) h
  refine ⟨D', hD', hl.symm, hp.symm, fun q hq => step_other hD' (by rw [hℓ]; exact Ne.symm hq),
    fun j => ?_⟩
  rcases hm j with ⟨h1, h2⟩ | h1
  · exact Or.inl ⟨h2, h1⟩
  · rcases mem_of_step h j with e | ⟨hτ, -, o, k, hact, -⟩
    · rcases mem_of_step hD' j with e' | ⟨hτ, -, o, k, hact, -⟩
      · exact Or.inl ⟨e', e⟩
      · rw [hℓ, ← hloc] at hact
        rw [hℓ] at hτ
        exact Or.inr ⟨h1.symm, hτ, o, k, hact⟩
    · rw [hℓ] at hτ hact
      exact Or.inr ⟨h1.symm, hτ, o, k, hact⟩

/-- **Commuting steps.** Steps of distinct processes commute unless both access the same object
and one of them changes it. -/
lemma step_comm {a b : P} (hab : a ≠ b) {C Ca Cab : Config A B P L} {ℓa ℓb : Label P A}
    (ha : ℓa.proc = a) (hb : ℓb.proc = b) (h1 : I.step C ℓa = some Ca)
    (h2 : I.step Ca ℓb = some Cab)
    (hnc : ∀ i o k j o' k', ℓa = .tau a → I.act a (C.loc a) = .access i o k → ℓb = .tau b →
      I.act b (C.loc b) = .access j o' k' →
        i ≠ j ∨ (((B i).δ (C.mem i) o).1 = C.mem i ∧ ((B j).δ (C.mem j) o').1 = C.mem j)) :
    ∃ Cb, I.step C ℓb = some Cb ∧ I.step Cb ℓa = some Cab := by
  have hbC : Ca.loc b = C.loc b ∧ Ca.pend b = C.pend b :=
    step_other h1 (by rw [ha]; exact hab)
  -- the object accessed by `b` is unchanged by `a`'s step
  have hobjb : ∀ j o' k', ℓb = .tau b → I.act b (Ca.loc b) = .access j o' k' →
      Ca.mem j = C.mem j := by
    intro j o' k' hℓb hact
    rw [hbC.1] at hact
    rcases mem_of_step h1 j with h | ⟨hℓa, -, o, k, hact', hv⟩
    · exact h
    · rw [ha] at hℓa hact'
      rcases hnc j o k j o' k' hℓa hact' hℓb hact with h | ⟨h, -⟩
      · exact absurd rfl h
      · rw [hv, h]
  obtain ⟨Cb, hCb, hl1, hp1, ho1, hm1⟩ := step_exact (I := I) hb hbC.1 hbC.2 hobjb h2
  have haCb : Cb.loc a = C.loc a ∧ Cb.pend a = C.pend a := ho1 a hab
  have hobja : ∀ i o k, ℓa = .tau a → I.act a (C.loc a) = .access i o k →
      C.mem i = Cb.mem i := by
    intro i o k hℓa hact
    rcases mem_of_step hCb i with h | ⟨hℓb, -, o', k', hact', hv⟩
    · exact h.symm
    · rw [hb] at hℓb hact'
      rcases hnc i o k i o' k' hℓa hact hℓb hact' with h | ⟨-, h⟩
      · exact absurd rfl h
      · rw [hv, h]
  obtain ⟨Cba, hCba, hl2, hp2, ho2, hm2⟩ := step_exact (I := I) ha haCb.1.symm haCb.2.symm
    hobja h1
  refine ⟨Cb, hCb, ?_⟩
  rw [hCba]
  congr 1
  have haCab : Cab.loc a = Ca.loc a ∧ Cab.pend a = Ca.pend a :=
    step_other h2 (by rw [hb]; exact Ne.symm hab)
  apply AgreeOn.univ_eq
  refine ⟨funext fun j => ?_, fun x _ => ?_, fun x _ => ?_⟩
  · rcases hm1 j with ⟨e1, e2⟩ | ⟨e1, hℓb, o', k', hact'⟩ <;>
      rcases hm2 j with ⟨e3, e4⟩ | ⟨e3, hℓa, o, k, hact⟩
    · rw [e3, e1, e2, ← e4]
    · rw [e3, e2]
    · rw [e3, e1]
    · -- both access `j`: both leave it unchanged
      rw [hbC.1] at hact'
      rcases hnc j o k j o' k' hℓa hact hℓb hact' with h | ⟨h, h'⟩
      · exact absurd rfl h
      · rw [e3, ← e1]
        rcases mem_of_step h1 j with f1 | ⟨-, -, o₁, k₁, hact₁, f1⟩ <;>
          rcases mem_of_step hCb j with f2 | ⟨-, -, o₂, k₂, hact₂, f2⟩
        · rw [f1, f2]
        · rw [hb] at hact₂; rw [hact'] at hact₂
          simp only [Action.access.injEq] at hact₂
          obtain ⟨-, ho, -⟩ := hact₂; rw [f1, f2, ← eq_of_heq ho, h']
        · rw [ha] at hact₁; rw [hact] at hact₁
          simp only [Action.access.injEq] at hact₁
          obtain ⟨-, ho, -⟩ := hact₁; rw [f1, f2, ← eq_of_heq ho, h]
        · rw [ha] at hact₁; rw [hact] at hact₁
          rw [hb] at hact₂; rw [hact'] at hact₂
          simp only [Action.access.injEq] at hact₁ hact₂
          obtain ⟨-, ho₁, -⟩ := hact₁; obtain ⟨-, ho₂, -⟩ := hact₂
          rw [f1, f2, ← eq_of_heq ho₁, ← eq_of_heq ho₂, h, h']
  · by_cases hxa : x = a
    · subst hxa; rw [hl2, ← haCab.1]
    · by_cases hxb : x = b
      · subst hxb; rw [(ho2 x hxa).1, hl1]
      · rw [(ho2 x hxa).1, (ho1 x hxb).1, (step_other h2 (by rw [hb]; exact Ne.symm hxb)).1,
          (step_other h1 (by rw [ha]; exact Ne.symm hxa)).1]
  · by_cases hxa : x = a
    · subst hxa; rw [hp2, ← haCab.2]
    · by_cases hxb : x = b
      · subst hxb; rw [(ho2 x hxa).2, hp1]
      · rw [(ho2 x hxa).2, (ho1 x hxb).2, (step_other h2 (by rw [hb]; exact Ne.symm hxb)).2,
          (step_other h1 (by rw [ha]; exact Ne.symm hxa)).2]

end Impl

end Cslib.SharedMemory
