/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Basic

/-!
# Basic lemmas about Herlihy–Wing histories

Counting lemmas for invocations and responses (`opsOf`, `ressOf`), restrictions to processes and
objects (`restrictP`, `restrictX`), complete sequential histories `seqHist`, and the identities
`idsOf` of the operations of a sequential history (`mem_idsOf`, `nodup_idsOf`,
`mem_zip_idsOf`).
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

/-! ### Counting invocations and responses -/

@[simp] lemma opsOf_nil (p : P) (x : X) : opsOf ([] : History P X Op Res) p x = [] := rfl
@[simp] lemma ressOf_nil (p : P) (x : X) : ressOf ([] : History P X Op Res) p x = [] := rfl

@[simp] lemma opsOf_append (H H' : History P X Op Res) (p : P) (x : X) :
    opsOf (H ++ H') p x = opsOf H p x ++ opsOf H' p x := by simp [opsOf]

@[simp] lemma ressOf_append (H H' : History P X Op Res) (p : P) (x : X) :
    ressOf (H ++ H') p x = ressOf H p x ++ ressOf H' p x := by simp [ressOf]

@[simp] lemma opsOf_cons (e : Event P X Op Res) (H : History P X Op Res) (p : P) (x : X) :
    opsOf (e :: H) p x = (e.invOf p x).toList ++ opsOf H p x := by
  cases h : e.invOf p x <;> simp [opsOf, h]

@[simp] lemma ressOf_cons (e : Event P X Op Res) (H : History P X Op Res) (p : P) (x : X) :
    ressOf (e :: H) p x = (e.resOf p x).toList ++ ressOf H p x := by
  cases h : e.resOf p x <;> simp [ressOf, h]

lemma Invoked.mono {H H' : History P X Op Res} {a : OpId P X} (h : Invoked H a) :
    Invoked (H ++ H') a := by
  simp only [Invoked, opsOf_append, List.length_append] at *; omega

lemma Completed.mono {H H' : History P X Op Res} {a : OpId P X} (h : Completed H a) :
    Completed (H ++ H') a := by
  simp only [Completed, ressOf_append, List.length_append] at *; omega

lemma opOf_append_of_invoked {H H' : History P X Op Res} {a : OpId P X} (h : Invoked H a) :
    opOf (H ++ H') a = opOf H a := by
  simp only [opOf, opsOf_append]; exact List.getElem?_append_left h

lemma resOf_append_of_completed {H H' : History P X Op Res} {a : OpId P X} (h : Completed H a) :
    resOf (H ++ H') a = resOf H a := by
  simp only [resOf, ressOf_append]; exact List.getElem?_append_left h

lemma invoked_iff_opOf {H : History P X Op Res} {a : OpId P X} :
    Invoked H a ↔ (opOf H a).isSome := by
  simp [Invoked, opOf]

lemma completed_iff_resOf {H : History P X Op Res} {a : OpId P X} :
    Completed H a ↔ (resOf H a).isSome := by
  simp [Completed, resOf]

lemma Invoked.of_opOf {H : History P X Op Res} {a : OpId P X} {o : Op} (h : opOf H a = some o) :
    Invoked H a := invoked_iff_opOf.2 (by simp [h])

lemma Completed.of_resOf {H : History P X Op Res} {a : OpId P X} {r : Res}
    (h : resOf H a = some r) : Completed H a := completed_iff_resOf.2 (by simp [h])

/-! ### Real-time order -/

lemma Precedes.mono {H H' : History P X Op Res} {a b : OpId P X} (h : Precedes H a b) :
    Precedes (H ++ H') a b := by
  obtain ⟨β, γ, rfl, h1, h2⟩ := h
  exact ⟨β, γ ++ H', by simp, h1, h2⟩

lemma Precedes.completed {H : History P X Op Res} {a b : OpId P X} (h : Precedes H a b) :
    Completed H a := by
  obtain ⟨β, γ, rfl, h1, -⟩ := h
  exact h1.mono

/-- Real-time precedence in an extension, towards an operation invoked before the extension,
already holds before the extension. -/
lemma Precedes.of_append_of_invoked {H H' : History P X Op Res} {a b : OpId P X}
    (h : Precedes (H ++ H') a b) (hb : Invoked H b) : Precedes H a b := by
  obtain ⟨β₁, γ, hsplit, h1, h2⟩ := h
  rcases List.append_eq_append_iff.1 hsplit with ⟨a', rfl, -⟩ | ⟨c', rfl, -⟩
  · exact absurd hb.mono h2
  · exact ⟨β₁, c', rfl, h1, h2⟩

lemma RT.precedes {H : History P X Op Res} {a b : OpId P X} (h : RT H a b) : Precedes H a b :=
  h.1

/-! ### Restrictions -/

omit [DecidableEq X] in
@[simp] lemma restrictP_nil (p : P) : restrictP ([] : History P X Op Res) p = [] := rfl
omit [DecidableEq P] in
@[simp] lemma restrictX_nil (x : X) : restrictX ([] : History P X Op Res) x = [] := rfl

omit [DecidableEq X] in
@[simp] lemma restrictP_append (H H' : History P X Op Res) (p : P) :
    restrictP (H ++ H') p = restrictP H p ++ restrictP H' p := by simp [restrictP]

omit [DecidableEq P] in
@[simp] lemma restrictX_append (H H' : History P X Op Res) (x : X) :
    restrictX (H ++ H') x = restrictX H x ++ restrictX H' x := by simp [restrictX]

omit [DecidableEq X] in
lemma restrictP_cons (e : Event P X Op Res) (H : History P X Op Res) (p : P) :
    restrictP (e :: H) p = (if e.proc = p then [e] else []) ++ restrictP H p := by
  by_cases h : e.proc = p <;> simp [restrictP, h]

omit [DecidableEq P] in
lemma restrictX_cons (e : Event P X Op Res) (H : History P X Op Res) (x : X) :
    restrictX (e :: H) x = (if e.obj = x then [e] else []) ++ restrictX H x := by
  by_cases h : e.obj = x <;> simp [restrictX, h]

omit [DecidableEq X] in
lemma restrictP_singleton (e : Event P X Op Res) (p : P) :
    restrictP [e] p = if e.proc = p then [e] else [] := by
  simp [restrictP_cons]

omit [DecidableEq P] in
lemma restrictX_singleton (e : Event P X Op Res) (x : X) :
    restrictX [e] x = if e.obj = x then [e] else [] := by
  simp [restrictX_cons]

/-- Filtering keeps the operations of `p` on `x` if it keeps all their events. -/
lemma opsOf_filter_of_true (H : History P X Op Res) (f : Event P X Op Res → Bool) (p : P) (x : X)
    (hf : ∀ e : Event P X Op Res, e.proc = p → e.obj = x → f e = true) :
    opsOf (H.filter f) p x = opsOf H p x := by
  induction H with
  | nil => rfl
  | cons e H ih =>
    by_cases he : f e = true
    · simp [he, ih]
    · have : e.invOf p x = none := by
        cases e with
        | inv q y o =>
          simp only [Event.invOf_inv, ite_eq_right_iff, reduceCtorEq, imp_false, not_and]
          rintro rfl rfl; exact he (hf _ rfl rfl)
        | res => rfl
      simp [he, ih, this]

lemma ressOf_filter_of_true (H : History P X Op Res) (f : Event P X Op Res → Bool) (p : P)
    (x : X) (hf : ∀ e : Event P X Op Res, e.proc = p → e.obj = x → f e = true) :
    ressOf (H.filter f) p x = ressOf H p x := by
  induction H with
  | nil => rfl
  | cons e H ih =>
    by_cases he : f e = true
    · simp [he, ih]
    · have : e.resOf p x = none := by
        cases e with
        | res q y o =>
          simp only [Event.resOf_res, ite_eq_right_iff, reduceCtorEq, imp_false, not_and]
          rintro rfl rfl; exact he (hf _ rfl rfl)
        | inv => rfl
      simp [he, ih, this]

/-- Filtering removes the operations of `p` on `x` if it removes all their events. -/
lemma opsOf_filter_of_false (H : History P X Op Res) (f : Event P X Op Res → Bool) (p : P)
    (x : X) (hf : ∀ e : Event P X Op Res, e.proc = p → e.obj = x → f e = false) :
    opsOf (H.filter f) p x = [] := by
  induction H with
  | nil => rfl
  | cons e H ih =>
    by_cases he : f e = true
    · have : e.invOf p x = none := by
        cases e with
        | inv q y o =>
          simp only [Event.invOf_inv, ite_eq_right_iff, reduceCtorEq, imp_false, not_and]
          rintro rfl rfl; simp [hf (.inv _ _ o) rfl rfl] at he
        | res => rfl
      simp [he, ih, this]
    · simp [he, ih]

lemma ressOf_filter_of_false (H : History P X Op Res) (f : Event P X Op Res → Bool) (p : P)
    (x : X) (hf : ∀ e : Event P X Op Res, e.proc = p → e.obj = x → f e = false) :
    ressOf (H.filter f) p x = [] := by
  induction H with
  | nil => rfl
  | cons e H ih =>
    by_cases he : f e = true
    · have : e.resOf p x = none := by
        cases e with
        | res q y o =>
          simp only [Event.resOf_res, ite_eq_right_iff, reduceCtorEq, imp_false, not_and]
          rintro rfl rfl; simp [hf (.res _ _ o) rfl rfl] at he
        | inv => rfl
      simp [he, ih, this]
    · simp [he, ih]

@[simp] lemma opsOf_restrictP (H : History P X Op Res) (p q : P) (x : X) :
    opsOf (restrictP H q) p x = if q = p then opsOf H p x else [] := by
  split_ifs with h
  · subst h; exact opsOf_filter_of_true _ _ _ _ (by intro e he _; simp [he])
  · exact opsOf_filter_of_false _ _ _ _ (by intro e he _; simp [he, Ne.symm h])

@[simp] lemma ressOf_restrictP (H : History P X Op Res) (p q : P) (x : X) :
    ressOf (restrictP H q) p x = if q = p then ressOf H p x else [] := by
  split_ifs with h
  · subst h; exact ressOf_filter_of_true _ _ _ _ (by intro e he _; simp [he])
  · exact ressOf_filter_of_false _ _ _ _ (by intro e he _; simp [he, Ne.symm h])

@[simp] lemma opsOf_restrictX (H : History P X Op Res) (p : P) (x y : X) :
    opsOf (restrictX H y) p x = if y = x then opsOf H p x else [] := by
  split_ifs with h
  · subst h; exact opsOf_filter_of_true _ _ _ _ (by intro e _ he; simp [he])
  · exact opsOf_filter_of_false _ _ _ _ (by intro e _ he; simp [he, Ne.symm h])

@[simp] lemma ressOf_restrictX (H : History P X Op Res) (p : P) (x y : X) :
    ressOf (restrictX H y) p x = if y = x then ressOf H p x else [] := by
  split_ifs with h
  · subst h; exact ressOf_filter_of_true _ _ _ _ (by intro e _ he; simp [he])
  · exact ressOf_filter_of_false _ _ _ _ (by intro e _ he; simp [he, Ne.symm h])

/-- Equivalent histories have the same operation instances. -/
lemma Equiv.opsOf_eq {H H' : History P X Op Res} (h : Equiv H H') (p : P) (x : X) :
    opsOf H p x = opsOf H' p x := by
  have := congrArg (fun H => opsOf H p x) (h p)
  simpa using this

lemma Equiv.ressOf_eq {H H' : History P X Op Res} (h : Equiv H H') (p : P) (x : X) :
    ressOf H p x = ressOf H' p x := by
  have := congrArg (fun H => ressOf H p x) (h p)
  simpa using this

/-! ### Complete sequential histories -/

omit [DecidableEq P] [DecidableEq X] in
@[simp] lemma seqHist_nil : seqHist ([] : List (OpRec P X Op Res)) = [] := rfl

omit [DecidableEq P] [DecidableEq X] in
@[simp] lemma seqHist_cons (e : OpRec P X Op Res) (M : List (OpRec P X Op Res)) :
    seqHist (e :: M) = .inv e.p e.x e.o :: .res e.p e.x e.r :: seqHist M := rfl

omit [DecidableEq P] [DecidableEq X] in
@[simp] lemma seqHist_append (M N : List (OpRec P X Op Res)) :
    seqHist (M ++ N) = seqHist M ++ seqHist N := by simp [seqHist]

omit [DecidableEq P] [DecidableEq X] in
lemma seqHist_singleton (e : OpRec P X Op Res) :
    seqHist [e] = [.inv e.p e.x e.o, .res e.p e.x e.r] := rfl

omit [DecidableEq P] [DecidableEq X] in
lemma filter_seqHist (M : List (OpRec P X Op Res)) (f : Event P X Op Res → Bool)
    (g : OpRec P X Op Res → Bool) (hfi : ∀ e, f (.inv e.p e.x e.o) = g e)
    (hfr : ∀ e, f (.res e.p e.x e.r) = g e) :
    (seqHist M).filter f = seqHist (M.filter g) := by
  induction M with
  | nil => rfl
  | cons e M ih =>
    by_cases h : g e = true
    · simp [hfi, hfr, h, ih]
    · simp [hfi, hfr, h, ih]

omit [DecidableEq X] in
lemma restrictP_seqHist (M : List (OpRec P X Op Res)) (p : P) :
    restrictP (seqHist M) p = seqHist (M.filter (·.p = p)) :=
  filter_seqHist M _ _ (fun _ => rfl) (fun _ => rfl)

omit [DecidableEq P] in
lemma restrictX_seqHist (M : List (OpRec P X Op Res)) (x : X) :
    restrictX (seqHist M) x = seqHist (M.filter (·.x = x)) :=
  filter_seqHist M _ _ (fun _ => rfl) (fun _ => rfl)

lemma opsOf_seqHist (M : List (OpRec P X Op Res)) (p : P) (x : X) :
    opsOf (seqHist M) p x =
      (M.filter (fun e => decide (e.p = p) && decide (e.x = x))).map (·.o) := by
  induction M with
  | nil => rfl
  | cons e M ih =>
    by_cases h : e.p = p ∧ e.x = x
    · simp [h, ih]
    · simp [h, ih]

lemma ressOf_seqHist (M : List (OpRec P X Op Res)) (p : P) (x : X) :
    ressOf (seqHist M) p x =
      (M.filter (fun e => decide (e.p = p) && decide (e.x = x))).map (·.r) := by
  induction M with
  | nil => rfl
  | cons e M ih =>
    by_cases h : e.p = p ∧ e.x = x
    · simp [h, ih]
    · simp [h, ih]

omit [DecidableEq P] [DecidableEq X] in
lemma seqHist_injective : Function.Injective (seqHist : List (OpRec P X Op Res) → _) := by
  intro M N h
  induction M generalizing N with
  | nil => cases N with
    | nil => rfl
    | cons => simp at h
  | cons e M ih => cases N with
    | nil => simp at h
    | cons f N =>
      simp only [seqHist_cons, List.cons.injEq, Event.inv.injEq, Event.res.injEq] at h
      obtain ⟨⟨h1, h2, h3⟩, ⟨-, -, h4⟩, h5⟩ := h
      rw [ih h5]
      cases e; cases f; simp_all

omit [DecidableEq P] [DecidableEq X] in
lemma seqHist_getLast? (M : List (OpRec P X Op Res)) :
    (seqHist M).getLast? = none ∨ ∃ e ∈ M, (seqHist M).getLast? = some (.res e.p e.x e.r) := by
  rcases List.eq_nil_or_concat M with rfl | ⟨L, e, rfl⟩
  · simp
  · right; exact ⟨e, by simp, by simp⟩

omit [DecidableEq P] [DecidableEq X] in
lemma seqHist_ne_concat_inv (M : List (OpRec P X Op Res)) (s : History P X Op Res) (p : P)
    (x : X) (o : Op) : seqHist M ≠ s ++ [.inv p x o] := by
  intro h
  rcases seqHist_getLast? M with h' | ⟨e, -, h'⟩ <;> simp [h] at h'

omit [DecidableEq P] [DecidableEq X] in
lemma seqHist_eq_concat_res {M : List (OpRec P X Op Res)} {s : History P X Op Res} {p : P}
    {x : X} {r : Res} (h : seqHist M = s ++ [.res p x r]) :
    ∃ M' o, M = M' ++ [⟨p, x, o, r⟩] ∧ s = seqHist M' ++ [.inv p x o] := by
  rcases List.eq_nil_or_concat M with rfl | ⟨L, e, rfl⟩
  · simp at h
  · simp only [List.concat_eq_append, seqHist_append, seqHist_singleton] at h
    have h' : (seqHist L ++ [Event.inv e.p e.x e.o]) ++ [.res e.p e.x e.r] = s ++ [.res p x r] := by
      simpa using h
    obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
    simp only [List.cons.injEq, Event.res.injEq, and_true] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    exact ⟨L, e.o, by simp, h1.symm⟩

omit [DecidableEq P] [DecidableEq X] in
/-- Prefixes of complete sequential histories. -/
lemma seqHist_eq_append {M : List (OpRec P X Op Res)} {β γ : History P X Op Res}
    (h : seqHist M = β ++ γ) :
    ∃ M₁ M₂, M = M₁ ++ M₂ ∧
      (β = seqHist M₁ ∨ ∃ e M₂', M₂ = e :: M₂' ∧ β = seqHist M₁ ++ [.inv e.p e.x e.o]) := by
  induction M generalizing β with
  | nil =>
    simp only [seqHist_nil, List.nil_eq_append_iff] at h
    exact ⟨[], [], rfl, Or.inl h.1⟩
  | cons e M ih =>
    rcases β with _ | ⟨f, β⟩
    · exact ⟨[], e :: M, rfl, Or.inl rfl⟩
    rcases β with _ | ⟨g, β⟩
    · simp only [seqHist_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
      exact ⟨[], e :: M, rfl, Or.inr ⟨e, M, rfl, by simp [h.1]⟩⟩
    simp only [seqHist_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl, h⟩ := h
    obtain ⟨M₁, M₂, rfl, hβ⟩ := ih h
    refine ⟨e :: M₁, M₂, rfl, ?_⟩
    rcases hβ with rfl | ⟨e', M₂', rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e', M₂', rfl, by simp⟩

/-! ### Identities of the operations of a sequential history -/

lemma cnt_eq_length (M : List (OpRec P X Op Res)) (p : P) (x : X) :
    cnt M p x = (M.filter (fun e => decide (e.p = p) && decide (e.x = x))).length := by
  simp [cnt, List.countP_eq_length_filter]

@[simp] lemma cnt_nil (p : P) (x : X) : cnt ([] : List (OpRec P X Op Res)) p x = 0 := rfl

@[simp] lemma cnt_append (M N : List (OpRec P X Op Res)) (p : P) (x : X) :
    cnt (M ++ N) p x = cnt M p x + cnt N p x := by simp [cnt]

lemma cnt_singleton (e : OpRec P X Op Res) (p : P) (x : X) :
    cnt [e] p x = if e.p = p ∧ e.x = x then 1 else 0 := by
  simp [cnt, List.countP_cons]

lemma length_opsOf_seqHist (M : List (OpRec P X Op Res)) (p : P) (x : X) :
    (opsOf (seqHist M) p x).length = cnt M p x := by
  simp [opsOf_seqHist, cnt_eq_length]

lemma length_ressOf_seqHist (M : List (OpRec P X Op Res)) (p : P) (x : X) :
    (ressOf (seqHist M) p x).length = cnt M p x := by
  simp [ressOf_seqHist, cnt_eq_length]

lemma idsGo_append (pre M N : List (OpRec P X Op Res)) :
    idsGo pre (M ++ N) = idsGo pre M ++ idsGo (pre ++ M) N := by
  induction M generalizing pre with
  | nil => simp [idsGo]
  | cons e M ih => simp [idsGo, ih]

lemma idsOf_append (M N : List (OpRec P X Op Res)) :
    idsOf (M ++ N) = idsOf M ++ idsGo M N := by
  simp [idsOf, idsGo_append]

@[simp] lemma idsOf_nil : idsOf ([] : List (OpRec P X Op Res)) = [] := rfl

lemma idsOf_concat (M : List (OpRec P X Op Res)) (e : OpRec P X Op Res) :
    idsOf (M ++ [e]) = idsOf M ++ [⟨e.p, e.x, cnt M e.p e.x⟩] := by
  simp [idsOf_append, idsGo]

@[simp] lemma length_idsGo (pre M : List (OpRec P X Op Res)) :
    (idsGo pre M).length = M.length := by
  induction M generalizing pre with
  | nil => rfl
  | cons e M ih => simp [idsGo, ih]

@[simp] lemma length_idsOf (M : List (OpRec P X Op Res)) : (idsOf M).length = M.length :=
  length_idsGo _ _

lemma mem_idsGo {pre M : List (OpRec P X Op Res)} {a : OpId P X} :
    a ∈ idsGo pre M ↔ cnt pre a.p a.x ≤ a.k ∧ a.k < cnt (pre ++ M) a.p a.x := by
  induction M generalizing pre with
  | nil => simp [idsGo]
  | cons e M ih =>
    simp only [idsGo, List.mem_cons, ih, List.append_assoc, List.singleton_append, cnt_append,
      cnt_singleton]
    rcases a with ⟨p, x, k⟩
    by_cases h : e.p = p ∧ e.x = x
    · obtain ⟨rfl, rfl⟩ := h
      simp only [OpId.mk.injEq, true_and, and_self, ↓reduceIte]
      have : cnt (e :: M) e.p e.x = 1 + cnt M e.p e.x := by
        rw [show e :: M = [e] ++ M from rfl, cnt_append, cnt_singleton]; simp
      rw [this]; omega
    · have : cnt (e :: M) p x = cnt M p x := by
        rw [show e :: M = [e] ++ M from rfl, cnt_append, cnt_singleton]; simp [h]
      simp only [this, h, ↓reduceIte, add_zero]
      constructor
      · rintro (h' | h')
        · simp only [OpId.mk.injEq] at h'; exact absurd ⟨h'.1.symm, h'.2.1.symm⟩ h
        · exact h'
      · exact Or.inr

lemma mem_idsOf {M : List (OpRec P X Op Res)} {a : OpId P X} :
    a ∈ idsOf M ↔ a.k < cnt M a.p a.x := by
  simp [idsOf, mem_idsGo]

lemma nodup_idsGo (pre M : List (OpRec P X Op Res)) : (idsGo pre M).Nodup := by
  induction M generalizing pre with
  | nil => simp [idsGo]
  | cons e M ih =>
    refine List.nodup_cons.2 ⟨?_, ih _⟩
    rw [mem_idsGo]
    simp [cnt_append, cnt_singleton]

lemma nodup_idsOf (M : List (OpRec P X Op Res)) : (idsOf M).Nodup := nodup_idsGo _ _

lemma invoked_seqHist {M : List (OpRec P X Op Res)} {a : OpId P X} :
    Invoked (seqHist M) a ↔ a ∈ idsOf M := by
  simp [Invoked, length_opsOf_seqHist, mem_idsOf]

lemma completed_seqHist {M : List (OpRec P X Op Res)} {a : OpId P X} :
    Completed (seqHist M) a ↔ a ∈ idsOf M := by
  simp [Completed, length_ressOf_seqHist, mem_idsOf]

/-- The operation identities of `M`, paired with the records. -/
lemma mem_zip_idsGo {pre M : List (OpRec P X Op Res)} {a : OpId P X} {e : OpRec P X Op Res}
    (h : (a, e) ∈ (idsGo pre M).zip M) : a.p = e.p ∧ a.x = e.x := by
  induction M generalizing pre with
  | nil => simp [idsGo] at h
  | cons f M ih =>
    simp only [idsGo, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨rfl, rfl⟩
    · exact ih h

lemma mem_zip_idsOf {M : List (OpRec P X Op Res)} {a : OpId P X} {e : OpRec P X Op Res}
    (h : (a, e) ∈ (idsOf M).zip M) : a.p = e.p ∧ a.x = e.x := mem_zip_idsGo h

end Cslib.SharedMemory.HerlihyWing
