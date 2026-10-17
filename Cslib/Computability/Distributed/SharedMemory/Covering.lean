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
