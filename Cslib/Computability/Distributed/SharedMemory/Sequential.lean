/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.LinPoints
public import Cslib.Computability.Distributed.SharedMemory.Model

/-!
# Sequential executions are linearizable only if they are legal

A *sequential execution* (`seqExec H`) runs operations one after another, each in isolation:
for every entry `(p, o, r, k)` of `H`, process `p` invokes `o`, takes `k` internal steps and
returns `r`. The only linearization of such an execution is the order of `H` itself, so a
sequential execution has a linearization only if `H` is legal for the sequential specification
(`IsLinearization.legal_of_seqExec`). Consequently, an implementation that admits a valid
sequential execution with an illegal response sequence is not linearizable
(`Impl.not_linearizable_of_seqExec`). Similarly, a completed operation whose response no state
of the specification produces witnesses non-linearizability (`Impl.not_linearizable_of_resp`).

`LegalFrom q H` is legality of a sequence of (operation, response) pairs; it is legality for the
specification viewed as a nondeterministic one (`legalFrom_iff_legal`). `legalFromB` is a
`Bool`-valued version, so that concrete instances can be decided by evaluation
(`legalFromB_eq_true_iff`).
-/

@[expose] public section

namespace Cslib.SharedMemory

open List

variable {P : Type} [DecidableEq P] {A : ObjSpec}

/-- One operation executed in isolation: invocation of `o` by `p`, `k` internal steps of `p`,
response `r`. -/
def segLabels (s : P × A.Op × A.Resp × ℕ) : List (Label P A) :=
  .inv s.1 s.2.1 :: (List.replicate s.2.2.2 (.tau s.1) ++ [.ret s.1 s.2.2.1])

/-- A sequential execution: operations executed one after another, each in isolation. -/
def seqExec (H : List (P × A.Op × A.Resp × ℕ)) : List (Label P A) := H.flatMap segLabels

/-- Legality of a sequence of (operation, response) pairs from state `q`. -/
def LegalFrom : A.State → List (A.Op × A.Resp) → Prop
  | _, [] => True
  | q, (o, r) :: H => (A.δ q o).2 = r ∧ LegalFrom (A.δ q o).1 H

/-- `Bool`-valued legality, for deciding concrete instances by evaluation. -/
def legalFromB [DecidableEq A.Resp] : A.State → List (A.Op × A.Resp) → Bool
  | _, [] => true
  | q, (o, r) :: H => decide ((A.δ q o).2 = r) && legalFromB (A.δ q o).1 H

lemma legalFromB_eq_true_iff [DecidableEq A.Resp] (q : A.State) (H : List (A.Op × A.Resp)) :
    legalFromB q H = true ↔ LegalFrom q H := by
  induction H generalizing q with
  | nil => simp [legalFromB, LegalFrom]
  | cons x H ih =>
    obtain ⟨o, r⟩ := x
    simp [legalFromB, LegalFrom, ih]

instance [DecidableEq A.Resp] (q : A.State) (H : List (A.Op × A.Resp)) :
    Decidable (LegalFrom q H) :=
  decidable_of_iff _ (legalFromB_eq_true_iff q H)

/-- Legality of a concatenation. -/
lemma legalFrom_append (q : A.State) (H₁ H₂ : List (A.Op × A.Resp)) :
    LegalFrom q (H₁ ++ H₂) ↔ LegalFrom q H₁ ∧ LegalFrom (A.runOps q (H₁.map Prod.fst)) H₂ := by
  induction H₁ generalizing q with
  | nil => simp [LegalFrom]
  | cons x H₁ ih =>
    obtain ⟨o, r⟩ := x
    simp [LegalFrom, ih, and_assoc]

/-- `LegalFrom` is legality for the specification viewed as a nondeterministic one. -/
lemma legalFrom_iff_legal (q : A.State) (H : List (A.Op × A.Resp)) :
    LegalFrom q H ↔ A.toNSpec.Legal q H := by
  induction H generalizing q with
  | nil => exact Iff.rfl
  | cons x H ih =>
    obtain ⟨o, r⟩ := x
    change (A.δ q o).2 = r ∧ LegalFrom (A.δ q o).1 H ↔
      ∃ q', A.δ q o = (q', r) ∧ A.toNSpec.Legal q' H
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨_, by rw [← h1], (ih _).1 h2⟩
    · rintro ⟨q', h1, h2⟩; rw [h1]; exact ⟨rfl, (ih _).2 h2⟩

/-! ## Invocations and responses of a sequential execution -/

omit [DecidableEq P] in
@[simp] lemma seqExec_nil : seqExec ([] : List (P × A.Op × A.Resp × ℕ)) = [] := rfl

omit [DecidableEq P] in
lemma seqExec_append (H₁ H₂ : List (P × A.Op × A.Resp × ℕ)) :
    seqExec (H₁ ++ H₂) = seqExec H₁ ++ seqExec H₂ := by
  simp [seqExec]

omit [DecidableEq P] in
lemma seqExec_concat (H : List (P × A.Op × A.Resp × ℕ)) (s : P × A.Op × A.Resp × ℕ) :
    seqExec (H ++ [s]) = seqExec H ++ segLabels s := by
  simp [seqExec]

lemma opsOf_segLabels (s : P × A.Op × A.Resp × ℕ) (p : P) :
    opsOf (segLabels s) p = if s.1 = p then [s.2.1] else [] := by
  have h : opsOf (List.replicate s.2.2.2 (.tau s.1) ++ [.ret s.1 s.2.2.1] : List (Label P A)) p
      = [] := by
    simp only [opsOf_append]
    simp [opsOf]
  rw [segLabels, opsOf_cons, h]
  by_cases hp : s.1 = p <;> simp [hp]

lemma respsOf_segLabels (s : P × A.Op × A.Resp × ℕ) (p : P) :
    respsOf (segLabels s) p = if s.1 = p then [s.2.2.1] else [] := by
  rw [segLabels, respsOf_cons, respsOf_append]
  have h : respsOf (List.replicate s.2.2.2 (.tau s.1) : List (Label P A)) p = [] := by
    simp [respsOf]
  rw [h]
  by_cases hp : s.1 = p <;> simp [hp]

/-- The operations invoked by `p` in a sequential execution. -/
lemma opsOf_seqExec (H : List (P × A.Op × A.Resp × ℕ)) (p : P) :
    opsOf (seqExec H) p = (H.filter (fun s => s.1 = p)).map (fun s => s.2.1) := by
  induction H with
  | nil => rfl
  | cons s H ih =>
    rw [show s :: H = [s] ++ H from rfl, seqExec_append, opsOf_append, ih]
    simp only [seqExec, flatMap_singleton, opsOf_segLabels]
    by_cases hp : s.1 = p <;> simp [hp]

/-- The responses returned by `p` in a sequential execution. -/
lemma respsOf_seqExec (H : List (P × A.Op × A.Resp × ℕ)) (p : P) :
    respsOf (seqExec H) p = (H.filter (fun s => s.1 = p)).map (fun s => s.2.2.1) := by
  induction H with
  | nil => rfl
  | cons s H ih =>
    rw [show s :: H = [s] ++ H from rfl, seqExec_append, respsOf_append, ih]
    simp only [seqExec, flatMap_singleton, respsOf_segLabels]
    by_cases hp : s.1 = p <;> simp [hp]

/-- In a sequential execution every invoked operation has completed. -/
lemma length_respsOf_seqExec (H : List (P × A.Op × A.Resp × ℕ)) (p : P) :
    (respsOf (seqExec H) p).length = (opsOf (seqExec H) p).length := by
  simp [opsOf_seqExec, respsOf_seqExec]

lemma completed_seqExec_iff {H : List (P × A.Op × A.Resp × ℕ)} {x : OpId P} :
    Completed (seqExec H) x ↔ Invoked (seqExec H) x := by
  simp [Completed, Invoked, length_respsOf_seqExec]

/-! ## The linearization of a sequential execution -/

lemma sublist_pair_of_sublist_concat {X : Type} {a b x : X} {l : List X}
    (h : [a, b].Sublist (l ++ [x])) (hb : b ≠ x) : [a, b].Sublist l := by
  obtain ⟨l₁, l₂, he, h₁, h₂⟩ := sublist_append_iff.1 h
  rcases (sublist_singleton.1 h₂) with rfl | rfl
  · rw [he, append_nil]; exact h₁
  · rcases l₁ with _ | ⟨c, l₁⟩
    · simp at he
    · simp only [cons_append, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      rcases l₁ with _ | ⟨d, l₁⟩
      · simp only [nil_append, cons.injEq] at he
        exact absurd he.1 hb
      · simp at he

/-- Strengthened form of `IsLinearization.legal_of_seqExec`: the linearization performs exactly
the operations of `H`, in order. -/
lemma IsLinearization.map_snd_and_legal_of_seqExec :
    ∀ {H : List (P × A.Op × A.Resp × ℕ)} {L : List (OpId P × A.Op)},
    IsLinearization (seqExec H) L →
      L.map Prod.snd = H.map (fun s => s.2.1) ∧
      LegalFrom A.init (H.map fun s => (s.2.1, s.2.2.1)) := by
  intro H
  induction H using List.reverseRecOn with
  | nil =>
    intro L hL
    have : L = [] := by
      rcases L with _ | ⟨y, L⟩
      · rfl
      · have := hL.op_eq y (by simp)
        simp [opOf, opsOf] at this
    subst this
    simp [LegalFrom]
  | append_singleton H s ih =>
    intro L hL
    obtain ⟨p, o, r, k⟩ := s
    set α := seqExec H with hα
    set α' := seqExec (H ++ [(p, o, r, k)]) with hα'
    have hαα : α' = α ++ segLabels (p, o, r, k) := seqExec_concat H _
    have hops : ∀ p', opsOf α' p' = opsOf α p' ++ if p = p' then [o] else [] := by
      intro p'; rw [hαα, opsOf_append, opsOf_segLabels]
    have hresps : ∀ p', respsOf α' p' = respsOf α p' ++ if p = p' then [r] else [] := by
      intro p'; rw [hαα, respsOf_append, respsOf_segLabels]
    set xs : OpId P := (p, (opsOf α p).length) with hxs
    have hxs_ninv : ¬ Invoked α xs := by simp [Invoked, hxs]
    have hxs_comp : Completed α' xs := by
      simp [Completed, hxs, hresps, length_respsOf_seqExec, hα]
    have hxs_resp : respOf α' xs = some r := by
      simp [respOf, hxs, hresps, ← length_respsOf_seqExec, hα]
    -- every other instance of `L` was invoked (hence completed) in `α`
    have hinv : ∀ y ∈ L.map Prod.fst, y ≠ xs → Invoked α y := by
      intro y hy hne
      have h1 := hL.invoked_of_mem hy
      obtain ⟨p', j⟩ := y
      simp only [Invoked, hops] at h1 ⊢
      by_cases hp : p = p'
      · subst hp
        simp only [↓reduceIte, length_append, length_singleton] at h1
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
        · exact h
        · exact absurd (by rw [hxs, h]) hne
      · simpa [hp] using h1
    -- hence they precede `xs`
    have hprec : ∀ y ∈ L.map Prod.fst, y ≠ xs → [y, xs].Sublist (L.map Prod.fst) := by
      intro y hy hne
      refine hL.realtime y xs ⟨α, segLabels (p, o, r, k), hαα, ?_, hxs_ninv⟩
        (hL.complete _ hxs_comp)
      exact completed_seqExec_iff.2 (hinv y hy hne)
    -- so `xs` is the last instance of `L`
    obtain ⟨e, he, hexs⟩ := mem_map.1 (hL.complete _ hxs_comp)
    obtain ⟨l₁, l₂, rfl⟩ := append_of_mem he
    have hl₂ : l₂ = [] := by
      rcases l₂ with _ | ⟨z, l₂⟩
      · rfl
      · exfalso
        have hnd := hL.nodup
        simp only [map_append, map_cons, hexs] at hnd
        have hz : z.1 ≠ xs := by
          intro h
          rw [nodup_append] at hnd
          exact (nodup_cons.1 hnd.2.1).1 (by simp [← h])
        have hzm : z.1 ∈ (l₁ ++ e :: z :: l₂).map Prod.fst := by simp
        have hs := hprec z.1 hzm hz
        simp only [map_append, map_cons, hexs] at hs
        have hzl₁ := mem_left_of_sublist_pair hnd hs
        rw [nodup_append] at hnd
        exact hnd.2.2 _ hzl₁ _ (by simp) rfl
    subst hl₂
    obtain ⟨x, o'⟩ := e
    simp only at hexs
    subst hexs
    have ho' : o' = o := by
      have := hL.op_eq _ (by simp : (xs, o') ∈ l₁ ++ [(xs, o')])
      simpa [opOf, hxs, hops] using this.symm
    subst o'
    have hnd := hL.nodup
    simp only [map_append, map_cons, map_nil] at hnd
    have hne : ∀ y ∈ l₁.map Prod.fst, y ≠ xs := by
      intro y hy h
      rw [nodup_append] at hnd
      exact hnd.2.2 _ hy _ (by simp) h
    have hinv₁ : ∀ y ∈ l₁, Invoked α y.1 := fun y hy =>
      hinv y.1 (by simp [mem_map_of_mem (f := Prod.fst) hy]) (hne _ (mem_map_of_mem hy))
    -- `l₁` is a linearization of `α`
    have hL₁ : IsLinearization α l₁ := by
      refine ⟨(nodup_append.1 hnd).1, ?_, ?_, ?_, ?_⟩
      · intro y hy
        rw [← opOf_append_of_invoked (β := segLabels (p, o, r, k)) (hinv₁ y hy), ← hαα]
        exact hL.op_eq y (by simp [hy])
      · intro a ha
        have h1 := hL.complete a (hαα ▸ ha.mono)
        simp only [map_append, map_cons, map_nil, mem_append, mem_singleton] at h1
        rcases h1 with h1 | rfl
        · exact h1
        · exact absurd (completed_seqExec_iff.1 ha) hxs_ninv
      · intro a b hab hb
        have h1 := hL.realtime a b (hαα ▸ hab.mono) (by simp [hb])
        simp only [map_append, map_cons, map_nil] at h1
        exact sublist_pair_of_sublist_concat h1 (hne b hb)
      · have h1 := hL.seq
        rw [seqOK_append] at h1
        refine (seqOK_congr _ _ fun y hy => ?_).1 h1.1
        rw [hαα]
        exact respOf_append_of_completed (completed_seqExec_iff.2 (hinv₁ y hy))
    obtain ⟨ih₁, ih₂⟩ := ih hL₁
    refine ⟨by simp [ih₁], ?_⟩
    rw [map_append, legalFrom_append]
    refine ⟨ih₂, ?_⟩
    have h1 := (seqOK_append _ _ _).1 hL.seq
    simp only [SeqOK, ih₁] at h1
    have h2 := h1.2.1 r hxs_resp
    simp only [map_map, map_cons, map_nil, LegalFrom, and_true, Function.comp_def]
    exact h2

/-- A sequential execution has a linearization only if its sequence of (operation, response)
pairs is legal for the sequential specification. -/
theorem IsLinearization.legal_of_seqExec {H : List (P × A.Op × A.Resp × ℕ)}
    {L : List (OpId P × A.Op)} (h : IsLinearization (seqExec H) L) :
    LegalFrom A.init (H.map fun s => (s.2.1, s.2.2.1)) :=
  (IsLinearization.map_snd_and_legal_of_seqExec h).2

/-- An implementation admitting a valid sequential execution with an illegal sequence of
responses is not linearizable. -/
theorem Impl.not_linearizable_of_seqExec {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}
    (I : Impl A B P L) {H : List (P × A.Op × A.Resp × ℕ)} (hv : I.Valid (seqExec H))
    (hl : ¬ LegalFrom A.init (H.map fun s => (s.2.1, s.2.2.1))) : ¬ I.Linearizable := by
  rintro ⟨h, hh⟩
  exact hl (hh _ hv).legal_of_seqExec

/-! ## Responses that no state can produce -/

lemma SeqOK.exists_state {α : List (Label P A)} :
    ∀ {q : A.State} {L : List (OpId P × A.Op)}, SeqOK α q L →
      ∀ {x : OpId P} {o : A.Op} {r : A.Resp}, (x, o) ∈ L → respOf α x = some r →
        ∃ q', (A.δ q' o).2 = r
  | _, [], _, _, _, _, hx, _ => by simp at hx
  | q, (y, o') :: L, h, x, o, r, hx, hr => by
    simp only [SeqOK] at h
    rcases List.mem_cons.1 hx with hx | hx
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
      exact ⟨q, h.1 r hr⟩
    · exact SeqOK.exists_state h.2 hx hr

/-- In a linearizable history, the response of every completed operation is a response the
sequential specification can give to it from *some* state. -/
theorem IsLinearization.exists_state_of_resp {α : List (Label P A)} {L : List (OpId P × A.Op)}
    (h : IsLinearization α L) {x : OpId P} {o : A.Op} {r : A.Resp}
    (ho : opOf α x = some o) (hr : respOf α x = some r) : ∃ q, (A.δ q o).2 = r := by
  have hc : Completed α x := by
    unfold respOf at hr; unfold Completed
    by_contra hlt
    rw [List.getElem?_eq_none (by omega)] at hr; cases hr
  obtain ⟨⟨x', o'⟩, hmem, hx'⟩ := List.mem_map.1 (h.complete x hc)
  simp only at hx'; subst hx'
  have : o' = o := by have := h.op_eq _ hmem; simp only at this; rw [ho] at this; cases this; rfl
  subst this
  exact SeqOK.exists_state h.seq hmem hr

/-- An implementation with a valid execution in which some completed operation returns a
response that no state of the specification produces is not linearizable. -/
theorem Impl.not_linearizable_of_resp {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}
    (I : Impl A B P L) {α : List (Label P A)} (hv : I.Valid α) {x : OpId P} {o : A.Op}
    {r : A.Resp} (ho : opOf α x = some o) (hr : respOf α x = some r)
    (hbad : ∀ q, (A.δ q o).2 ≠ r) : ¬ I.Linearizable := by
  rintro ⟨h, hh⟩
  obtain ⟨q, hq⟩ := (hh _ hv).exists_state_of_resp ho hr
  exact hbad q hq

end Cslib.SharedMemory
