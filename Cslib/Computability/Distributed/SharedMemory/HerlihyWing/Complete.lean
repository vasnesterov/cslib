/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Seq

/-!
# `complete(H)`: removing pending invocations

## Main results

* `completeAux_append`, `completeAux_eq_append`: `complete` and splittings of a history.
* `ressOf_completeAux`, `opsOf_completeAux_sublist`: responses are kept, invocations may be
  dropped.
* `restrictP_completeAux`: `complete` commutes with restriction to a process.
* `WellFormed.restrictP_complete`: for a well-formed history, `complete(H)|p` is `H|p` without
  its pending invocation; consequences `invoked_complete`, `opOf_complete`, `completed_complete`,
  `resOf_complete`.
* `WellFormed.precedes_complete_iff`: real-time precedence towards an operation of `H` is the
  same in `H` and in `complete(H)`.
* `precedes_restrictP_iff`: real-time precedence among operations of one process is the same in
  `H` and in `H|p`.
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

/-! ### Restriction lemmas for instances -/

lemma completed_restrictP {H : History P X Op Res} {q : P} {a : OpId P X} :
    Completed (restrictP H q) a ↔ q = a.p ∧ Completed H a := by
  simp only [Completed, ressOf_restrictP]; split_ifs with h <;> simp [h]

lemma invoked_restrictP {H : History P X Op Res} {q : P} {a : OpId P X} :
    Invoked (restrictP H q) a ↔ q = a.p ∧ Invoked H a := by
  simp only [Invoked, opsOf_restrictP]; split_ifs with h <;> simp [h]

lemma opOf_restrictP {H : History P X Op Res} {a : OpId P X} :
    opOf (restrictP H a.p) a = opOf H a := by
  simp [opOf]

lemma resOf_restrictP {H : History P X Op Res} {a : OpId P X} :
    resOf (restrictP H a.p) a = resOf H a := by
  simp [resOf]

lemma Equiv.completed_iff {H H' : History P X Op Res} (h : Equiv H H') {a : OpId P X} :
    Completed H a ↔ Completed H' a := by
  simp [Completed, h.ressOf_eq]

lemma Equiv.opOf_eq {H H' : History P X Op Res} (h : Equiv H H') (a : OpId P X) :
    opOf H a = opOf H' a := by
  simp [opOf, h.opsOf_eq]

lemma Equiv.resOf_eq {H H' : History P X Op Res} (h : Equiv H H') (a : OpId P X) :
    resOf H a = resOf H' a := by
  simp [resOf, h.ressOf_eq]

/-- Real-time precedence among instances of one process can be read off its subhistory. -/
lemma precedes_restrictP_iff {H : History P X Op Res} {p : P} {a b : OpId P X} (ha : a.p = p)
    (hb : b.p = p) : Precedes (restrictP H p) a b ↔ Precedes H a b := by
  subst ha
  constructor
  · rintro ⟨β', γ', h, h1, h2⟩
    obtain ⟨β, γ, rfl, rfl, rfl⟩ := List.filter_eq_append_iff.1 h
    refine ⟨β, γ, rfl, (completed_restrictP.1 h1).2, fun h' => h2 ?_⟩
    exact invoked_restrictP.2 ⟨hb.symm, h'⟩
  · rintro ⟨β, γ, rfl, h1, h2⟩
    refine ⟨restrictP β a.p, restrictP γ a.p, restrictP_append _ _ _,
      completed_restrictP.2 ⟨rfl, h1⟩, fun h' => h2 (invoked_restrictP.1 h').2⟩

/-! ### `completeAux` -/

lemma opsOf_eq_nil_of_isRes {R : History P X Op Res} (hR : ∀ e ∈ R, e.isRes = true) (p : P)
    (x : X) : opsOf R p x = [] := by
  induction R with
  | nil => rfl
  | cons e R ih =>
    rw [opsOf_cons, ih (fun f hf => hR f (List.mem_cons_of_mem _ hf))]
    cases e with
    | inv => simp at hR
    | res => rfl

omit [DecidableEq X] in
@[simp] lemma completeAux_nil (γ : History P X Op Res) : completeAux [] γ = [] := rfl

omit [DecidableEq X] in
lemma completeAux_cons (e : Event P X Op Res) (β γ : History P X Op Res) :
    completeAux (e :: β) γ =
      if keep e (β ++ γ) then e :: completeAux β γ else completeAux β γ := rfl

omit [DecidableEq X] in
lemma completeAux_append (β γ δ : History P X Op Res) :
    completeAux (β ++ γ) δ = completeAux β (γ ++ δ) ++ completeAux γ δ := by
  induction β with
  | nil => rfl
  | cons e β ih =>
    simp only [List.cons_append, completeAux_cons, List.append_assoc, ih]
    split_ifs <;> rfl

omit [DecidableEq X] in
lemma complete_append (β γ : History P X Op Res) :
    complete (β ++ γ) = completeAux β γ ++ complete γ := by
  simp [complete, completeAux_append]

omit [DecidableEq X] in
/-- Splittings of `completeAux β γ` come from splittings of `β`. -/
lemma completeAux_eq_append {β γ β₁' β₂' : History P X Op Res}
    (h : completeAux β γ = β₁' ++ β₂') :
    ∃ β₁ β₂, β = β₁ ++ β₂ ∧ β₁' = completeAux β₁ (β₂ ++ γ) ∧ β₂' = completeAux β₂ γ := by
  induction β generalizing β₁' with
  | nil =>
    simp only [completeAux_nil, List.nil_eq_append_iff] at h
    exact ⟨[], [], rfl, h.1, h.2⟩
  | cons e β ih =>
    rw [completeAux_cons] at h
    split_ifs at h with hk
    · rcases List.cons_eq_append_iff.1 h with ⟨rfl, h'⟩ | ⟨β₁'', rfl, h'⟩
      · exact ⟨[], e :: β, rfl, rfl, by simp [completeAux_cons, hk, h']⟩
      · obtain ⟨b1, b2, rfl, rfl, rfl⟩ := ih h'
        refine ⟨e :: b1, b2, rfl, ?_, rfl⟩
        have hk' : keep e (b1 ++ (b2 ++ γ)) = true := by simpa using hk
        simp [completeAux_cons, hk']
    · obtain ⟨b1, b2, rfl, rfl, rfl⟩ := ih h
      refine ⟨e :: b1, b2, rfl, ?_, rfl⟩
      have hk' : ¬ keep e (b1 ++ (b2 ++ γ)) = true := by simpa using hk
      simp [completeAux_cons, hk']

omit [DecidableEq X] in
lemma completeAux_sublist (β γ : History P X Op Res) : (completeAux β γ).Sublist β := by
  induction β with
  | nil => exact List.Sublist.slnil
  | cons e β ih =>
    rw [completeAux_cons]; split_ifs
    · exact ih.cons_cons e
    · exact ih.cons e

lemma opsOf_completeAux_sublist (β γ : History P X Op Res) (p : P) (x : X) :
    (opsOf (completeAux β γ) p x).Sublist (opsOf β p x) :=
  (completeAux_sublist β γ).filterMap _

@[simp] lemma ressOf_completeAux (β γ : History P X Op Res) (p : P) (x : X) :
    ressOf (completeAux β γ) p x = ressOf β p x := by
  induction β with
  | nil => rfl
  | cons e β ih =>
    rw [completeAux_cons]; split_ifs with hk
    · simp [ih]
    · cases e with
      | inv => simp [ih]
      | res => simp [keep] at hk

@[simp] lemma completed_completeAux {β γ : History P X Op Res} {a : OpId P X} :
    Completed (completeAux β γ) a ↔ Completed β a := by
  simp [Completed]

@[simp] lemma completed_complete {H : History P X Op Res} {a : OpId P X} :
    Completed (complete H) a ↔ Completed H a := completed_completeAux

@[simp] lemma resOf_complete (H : History P X Op Res) (a : OpId P X) :
    resOf (complete H) a = resOf H a := by
  simp [resOf, complete]

omit [DecidableEq X] in
lemma restrictP_completeAux (β γ : History P X Op Res) (p : P) :
    restrictP (completeAux β γ) p = completeAux (restrictP β p) (restrictP γ p) := by
  induction β with
  | nil => rfl
  | cons e β ih =>
    rw [completeAux_cons]
    by_cases he : e.proc = p
    · have hk : keep e (β ++ γ) = keep e (restrictP β p ++ restrictP γ p) := by
        rw [← restrictP_append]
        subst he; simp [keep, restrictP, List.any_filter]
      split_ifs with h1
      · simp only [restrictP_cons, he, ↓reduceIte, List.singleton_append, completeAux_cons, ← hk,
          h1, ih]
      · simp only [restrictP_cons, he, ↓reduceIte, List.singleton_append, completeAux_cons, ← hk,
          h1, ih, Bool.false_eq_true]
    · split_ifs with h1
      · simp [restrictP_cons, he, ih]
      · simp [restrictP_cons, he, ih]

omit [DecidableEq X] in
lemma restrictP_complete (H : History P X Op Res) (p : P) :
    restrictP (complete H) p = complete (restrictP H p) :=
  restrictP_completeAux H [] p

omit [DecidableEq X] in
@[simp] lemma completeAux_seqHist (M : List (OpRec P X Op Res)) (γ : History P X Op Res) :
    completeAux (seqHist M) γ = seqHist M := by
  induction M with
  | nil => rfl
  | cons e M ih =>
    simp only [seqHist_cons, completeAux_cons, keep, Event.isRes_inv, Event.isRes_res,
      Bool.true_or, ↓reduceIte, ih, List.cons_append, List.any_cons, Event.proc_res,
      Event.proc_inv, decide_true, Bool.false_or]

omit [DecidableEq X] in
lemma complete_concat_inv (M : List (OpRec P X Op Res)) (p : P) (x : X) (o : Op) :
    complete (seqHist M ++ [.inv p x o]) = seqHist M := by
  rw [complete_append, completeAux_seqHist]; simp [complete, completeAux_cons, keep]

omit [DecidableEq X] in
/-- If all events belong to one process and something follows `β`, nothing of `β` is
dropped. -/
lemma completeAux_of_proc {β γ : History P X Op Res} {p : P}
    (h : ∀ e ∈ β ++ γ, e.proc = p) (hγ : γ ≠ []) : completeAux β γ = β := by
  induction β with
  | nil => rfl
  | cons e β ih =>
    have hk : keep e (β ++ γ) = true := by
      obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil γ hγ
      simp only [keep, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨f, by simp [hf], by rw [h f (by simp [hf]), h e (by simp)]⟩
    rw [completeAux_cons, ih (fun f hf => h f (by simp [hf]))]; simp [hk]

/-! ### `complete` of a well-formed history -/

omit [DecidableEq X] in
/-- For a well-formed `H`, `complete(H)|p` is `H|p` without its pending invocation. -/
lemma WellFormed.restrictP_complete {H : History P X Op Res} (hH : WellFormed H) (p : P) :
    ∃ M : List (OpRec P X Op Res), restrictP (complete H) p = seqHist M ∧
      (restrictP H p = seqHist M ∨ ∃ x o, restrictP H p = seqHist M ++ [.inv p x o]) := by
  obtain ⟨M, -, h⟩ := hH.restrictP_eq p
  refine ⟨M, ?_, h⟩
  rw [Cslib.SharedMemory.HerlihyWing.restrictP_complete]
  rcases h with h | ⟨x, o, h⟩
  · rw [h]; exact completeAux_seqHist M []
  · rw [h]; exact complete_concat_inv M p x o

lemma WellFormed.opsOf_complete {H : History P X Op Res} (hH : WellFormed H) (p : P) (x : X) :
    opsOf (complete H) p x <+: opsOf H p x ∧
      (opsOf (complete H) p x).length = (ressOf H p x).length := by
  obtain ⟨M, hc, h⟩ := hH.restrictP_complete p
  rw [opsOf_eq_restrictP, hc, opsOf_eq_restrictP H, ressOf_eq_restrictP]
  rcases h with h | ⟨y, o, h⟩
  · rw [h]; exact ⟨List.prefix_refl _, by rw [length_opsOf_seqHist, length_ressOf_seqHist]⟩
  · rw [h, opsOf_append, ressOf_append]
    refine ⟨List.prefix_append _ _, ?_⟩
    simp [length_opsOf_seqHist, length_ressOf_seqHist]

lemma WellFormed.invoked_complete {H : History P X Op Res} (hH : WellFormed H) {a : OpId P X} :
    Invoked (complete H) a ↔ Completed H a := by
  simp [Invoked, Completed, (hH.opsOf_complete a.p a.x).2]

lemma WellFormed.opOf_complete {H : History P X Op Res} (hH : WellFormed H) {a : OpId P X}
    (ha : Completed H a) : opOf (complete H) a = opOf H a := by
  obtain ⟨⟨l, hl⟩, hlen⟩ := hH.opsOf_complete a.p a.x
  simp only [opOf, ← hl]
  exact (List.getElem?_append_left (by rw [hlen]; exact ha)).symm

/-- Key lemma for `WellFormed.precedes_complete_iff`: an invocation (in `β`) of an operation
that completes in `β ++ γ` is kept by `complete`. -/
lemma WellFormed.invoked_completeAux {β γ : History P X Op Res} (hH : WellFormed (β ++ γ))
    {b : OpId P X} (hc : Completed (β ++ γ) b) (hi : Invoked β b) :
    Invoked (completeAux β γ) b := by
  have key : Invoked (completeAux β γ) b ↔
      Invoked (completeAux (restrictP β b.p) (restrictP γ b.p)) b := by
    rw [← restrictP_completeAux, invoked_restrictP]; simp
  rw [key]
  by_cases hγ : restrictP γ b.p = []
  · have h1 : completeAux (restrictP β b.p) (restrictP γ b.p) = restrictP (complete β) b.p := by
      rw [hγ, Cslib.SharedMemory.HerlihyWing.restrictP_complete]; rfl
    rw [h1, invoked_restrictP, (hH.of_append).invoked_complete]
    refine ⟨rfl, ?_⟩
    have : ressOf γ b.p b.x = [] := by rw [ressOf_eq_restrictP, hγ]; rfl
    simpa [Completed, this] using hc
  · rw [completeAux_of_proc (p := b.p) ?_ hγ]
    · exact invoked_restrictP.2 ⟨rfl, hi⟩
    · intro e he
      rw [← restrictP_append] at he
      exact of_decide_eq_true (List.mem_filter.1 he).2

/-- Real-time precedence towards an operation of a well-formed `H` is the same in `H` and in
`complete(H)`. -/
lemma WellFormed.precedes_complete_iff {H : History P X Op Res} (hH : WellFormed H)
    {a b : OpId P X} (hb : Completed H b) : Precedes (complete H) a b ↔ Precedes H a b := by
  constructor
  · rintro ⟨β', γ', h, h1, h2⟩
    obtain ⟨β, γ, rfl, rfl, rfl⟩ := completeAux_eq_append h
    rw [List.append_nil] at h1 h2
    exact ⟨β, γ, rfl, completed_completeAux.1 h1,
      fun h' => h2 (hH.invoked_completeAux hb h')⟩
  · rintro ⟨β, γ, rfl, h1, h2⟩
    refine ⟨completeAux β γ, complete γ, complete_append β γ, completed_completeAux.2 h1, ?_⟩
    intro h'
    apply h2
    exact lt_of_lt_of_le h' (opsOf_completeAux_sublist β γ b.p b.x).length_le

end Cslib.SharedMemory.HerlihyWing
