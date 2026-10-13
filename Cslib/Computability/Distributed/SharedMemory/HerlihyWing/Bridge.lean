/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Equiv
public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.DetSpec
public import Cslib.Computability.Distributed.SharedMemory.Linearization

/-!
# Herlihy–Wing linearizability vs. shared-memory linearizability

The shared-memory model `Cslib.SharedMemory` records executions of implementations of a single
deterministic object `A : ObjSpec` as lists of labels (`inv p o`, `ret p r`, `tau p`) and
defines linearizability by an explicit list of operation instances
(`Cslib.SharedMemory.IsLinearization`): duplicate-free, with the invoked operations, containing
every completed instance, legal, and respecting real-time order *towards every linearized
instance, including pending ones*.

We show that this is exactly the amended definition of Sela–Herlihy–Petrank
(Definition 4.1, `Cslib.SharedMemory.HerlihyWing.Linearizable`) for the single object
`X = Unit`. Inside the namespace `Cslib.SharedMemory.HerlihyWing`, the notions of the
shared-memory model that are shadowed by Herlihy–Wing notions of the same name (`OpId`,
`WellFormed`, `Precedes`, `Invoked`, `Completed`, …) are referred to as `SharedMemory.OpId`,
`SharedMemory.WellFormed`, etc.

## Main definitions

* `toHist α`: the history of an execution (internal steps dropped); `ofHist H`, with
  `toHist (ofHist H) = H`.
* `specOf A`: the sequential specification of the deterministic object `A`.
* `cid`, `uid`: operation instances `(p, k) ↦ ⟨p, (), k⟩` and back.

## Main results

* Transfer lemmas: `opsOf_toHist`, `ressOf_toHist`, `opOf_toHist`, `resOf_toHist`,
  `invoked_toHist`, `completed_toHist`, `precedes_toHist`, `wellFormed_toHist_iff`.
* `isLinearization_iff_isLinA`, `cslib_linearizable_iff`, `linearizable_iff_cslib`:
  `SharedMemory.IsLinearization` is the amended definition of linearizability.

## References

* [G. Sela, M. Herlihy, E. Petrank, *Brief Announcement: Linearizability: A
  Typo*][SelaHerlihyPetrank2021]
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

variable {P : Type} [DecidableEq P] {A : ObjSpec}

/-! ### Histories of executions -/

/-- The events of a label (internal steps have none). -/
def labelEvents : Label P A → History P Unit A.Op A.Resp
  | .inv p o => [.inv p () o]
  | .ret p r => [.res p () r]
  | .tau _ => []

/-- The history of an execution, as a history of the single object `()`. -/
def toHist (α : List (Label P A)) : History P Unit A.Op A.Resp := α.flatMap labelEvents

/-- The label of an event. -/
def eventLabel : Event P Unit A.Op A.Resp → Label P A
  | .inv p _ o => .inv p o
  | .res p _ r => .ret p r

/-- A history of the single object `()`, as an execution without internal steps. -/
def ofHist (H : History P Unit A.Op A.Resp) : List (Label P A) := H.map eventLabel

/-- The sequential specification of the deterministic object `A`. -/
def specOf (A : ObjSpec) : SeqSpec P Unit A.Op A.Resp := fun _ => detSpec A.init A.δ

/-- The operation instance `(p, k)` of `SharedMemory` as an instance of the object `()`. -/
def cid (a : SharedMemory.OpId P) : OpId P Unit := ⟨a.1, (), a.2⟩

/-- An instance of the object `()` as an operation instance of `SharedMemory`. -/
def uid (a : OpId P Unit) : SharedMemory.OpId P := (a.p, a.k)

omit [DecidableEq P] in
@[simp] lemma uid_cid (a : SharedMemory.OpId P) : uid (cid a) = a := rfl
omit [DecidableEq P] in
@[simp] lemma cid_uid (a : OpId P Unit) : cid (uid a) = a := by cases a; rfl

omit [DecidableEq P] in
lemma cid_injective : Function.Injective (cid : SharedMemory.OpId P → OpId P Unit) :=
  fun a b h => by simpa using congrArg uid h

omit [DecidableEq P] in
lemma uid_injective : Function.Injective (uid : OpId P Unit → SharedMemory.OpId P) :=
  fun a b h => by simpa using congrArg cid h

omit [DecidableEq P] in
@[simp] lemma toHist_nil : toHist ([] : List (Label P A)) = [] := rfl

omit [DecidableEq P] in
@[simp] lemma toHist_cons (ℓ : Label P A) (α : List (Label P A)) :
    toHist (ℓ :: α) = labelEvents ℓ ++ toHist α := rfl

omit [DecidableEq P] in
@[simp] lemma toHist_append (α β : List (Label P A)) :
    toHist (α ++ β) = toHist α ++ toHist β := by simp [toHist]

omit [DecidableEq P] in
@[simp] lemma toHist_ofHist (H : History P Unit A.Op A.Resp) :
    toHist (ofHist H : List (Label P A)) = H := by
  induction H with
  | nil => rfl
  | cons e H ih => cases e <;> simp_all [ofHist, eventLabel, labelEvents]

/-! ### Transfer lemmas -/

@[simp] lemma opsOf_toHist (α : List (Label P A)) (p : P) (x : Unit) :
    opsOf (toHist α) p x = SharedMemory.opsOf α p := by
  induction α with
  | nil => rfl
  | cons ℓ α ih =>
    cases ℓ with
    | inv q o => by_cases h : q = p <;> simp [labelEvents, ih, h]
    | ret q r => simp [labelEvents, ih]
    | tau q => simp [labelEvents, ih]

@[simp] lemma ressOf_toHist (α : List (Label P A)) (p : P) (x : Unit) :
    ressOf (toHist α) p x = SharedMemory.respsOf α p := by
  induction α with
  | nil => rfl
  | cons ℓ α ih =>
    cases ℓ with
    | inv q o => simp [labelEvents, ih]
    | ret q r => by_cases h : q = p <;> simp [labelEvents, ih, h]
    | tau q => simp [labelEvents, ih]

lemma opOf_toHist (α : List (Label P A)) (a : OpId P Unit) :
    opOf (toHist α) a = SharedMemory.opOf α (uid a) := by
  simp [opOf, SharedMemory.opOf, uid]

lemma resOf_toHist (α : List (Label P A)) (a : OpId P Unit) :
    resOf (toHist α) a = SharedMemory.respOf α (uid a) := by
  simp [resOf, SharedMemory.respOf, uid]

lemma invoked_toHist (α : List (Label P A)) (a : OpId P Unit) :
    Invoked (toHist α) a ↔ SharedMemory.Invoked α (uid a) := by
  simp [Invoked, SharedMemory.Invoked, uid]

lemma completed_toHist (α : List (Label P A)) (a : OpId P Unit) :
    Completed (toHist α) a ↔ SharedMemory.Completed α (uid a) := by
  simp [Completed, SharedMemory.Completed, uid]

omit [DecidableEq P] in
/-- Lifting a split of the history to a split of the execution, at an event. -/
lemma toHist_eq_append_cons {α : List (Label P A)} {β' γ' : History P Unit A.Op A.Resp}
    {e : Event P Unit A.Op A.Resp} (h : toHist α = β' ++ e :: γ') :
    ∃ β ℓ γ, α = β ++ ℓ :: γ ∧ toHist β = β' ∧ labelEvents ℓ = [e] ∧ toHist γ = γ' := by
  induction α generalizing β' with
  | nil => simp at h
  | cons ℓ α ih =>
    cases ℓ with
    | tau q =>
      obtain ⟨β, ℓ, γ, rfl, h1, h2, h3⟩ := ih (by simpa [labelEvents] using h)
      exact ⟨.tau q :: β, ℓ, γ, rfl, by simpa [labelEvents] using h1, h2, h3⟩
    | inv q o =>
      rcases β' with _ | ⟨f, β'⟩
      · simp only [toHist_cons, labelEvents, List.singleton_append, List.nil_append,
          List.cons.injEq] at h
        exact ⟨[], _, α, rfl, rfl, by simp [labelEvents, h.1], h.2⟩
      · simp only [toHist_cons, labelEvents, List.cons_append,
          List.cons.injEq] at h
        obtain ⟨β, ℓ, γ, rfl, h1, h2, h3⟩ := ih h.2
        exact ⟨.inv q o :: β, ℓ, γ, rfl, by simp [labelEvents, h1, h.1], h2, h3⟩
    | ret q r =>
      rcases β' with _ | ⟨f, β'⟩
      · simp only [toHist_cons, labelEvents, List.singleton_append, List.nil_append,
          List.cons.injEq] at h
        exact ⟨[], _, α, rfl, rfl, by simp [labelEvents, h.1], h.2⟩
      · simp only [toHist_cons, labelEvents, List.cons_append,
          List.cons.injEq] at h
        obtain ⟨β, ℓ, γ, rfl, h1, h2, h3⟩ := ih h.2
        exact ⟨.ret q r :: β, ℓ, γ, rfl, by simp [labelEvents, h1, h.1], h2, h3⟩

omit [DecidableEq P] in
/-- Lifting a split of the history to a split of the execution. -/
lemma toHist_eq_append {α : List (Label P A)} {β' γ' : History P Unit A.Op A.Resp}
    (h : toHist α = β' ++ γ') : ∃ β γ, α = β ++ γ ∧ toHist β = β' ∧ toHist γ = γ' := by
  rcases γ' with _ | ⟨e, γ'⟩
  · exact ⟨α, [], by simp, by simpa using h, rfl⟩
  · obtain ⟨β, ℓ, γ, rfl, h1, h2, h3⟩ := toHist_eq_append_cons h
    exact ⟨β, ℓ :: γ, rfl, h1, by simp [h2, h3]⟩

lemma precedes_toHist (α : List (Label P A)) (a b : OpId P Unit) :
    Precedes (toHist α) a b ↔ SharedMemory.Precedes α (uid a) (uid b) := by
  constructor
  · rintro ⟨β', γ', h, h1, h2⟩
    obtain ⟨β, γ, rfl, rfl, rfl⟩ := toHist_eq_append h
    exact ⟨β, γ, rfl, (completed_toHist _ _).1 h1, fun h => h2 ((invoked_toHist _ _).2 h)⟩
  · rintro ⟨β, γ, rfl, h1, h2⟩
    exact ⟨toHist β, toHist γ, by simp, (completed_toHist _ _).2 h1,
      fun h => h2 ((invoked_toHist _ _).1 h)⟩

lemma precedes_toHist' (α : List (Label P A)) (a b : SharedMemory.OpId P) :
    Precedes (toHist α) (cid a) (cid b) ↔ SharedMemory.Precedes α a b := by
  simpa using precedes_toHist α (cid a) (cid b)

/-! ### Well-formedness -/

/-- Generic: a property of all splits `β ++ e :: γ` of `l ++ [a]`. -/
lemma forall_split_concat {T : Type*} {l : List T} {a : T} {C : List T → T → Prop} :
    (∀ β e γ, l ++ [a] = β ++ e :: γ → C β e) ↔ (∀ β e γ, l = β ++ e :: γ → C β e) ∧ C l a := by
  constructor
  · intro h
    exact ⟨fun β e γ hl => h β e (γ ++ [a]) (by simp [hl]), h l a [] rfl⟩
  · rintro ⟨h, ha⟩ β e γ hl
    rcases List.eq_nil_or_concat γ with rfl | ⟨γ₀, c, rfl⟩
    · obtain ⟨rfl, h2⟩ := List.append_inj' (show l ++ [a] = β ++ [e] by simpa using hl) rfl
      simp only [List.cons.injEq, and_true] at h2; subst h2; exact ha
    · have hl' : l ++ [a] = (β ++ e :: γ₀) ++ [c] := by simpa using hl
      exact h β e γ₀ (List.append_inj' hl' rfl).1

/-- The condition of `SharedMemory.WellFormed` at the event `e` after the history `H` (single
object `()`): an invocation of `p` requires all operations of `p` to have completed, a response
to `p` requires exactly one pending operation of `p`. -/
def StepOK {Op Res : Type} (H : History P Unit Op Res) : Event P Unit Op Res → Prop
  | .inv p _ _ => (opsOf H p ()).length = (ressOf H p ()).length
  | .res p _ _ => (opsOf H p ()).length = (ressOf H p ()).length + 1

lemma restrictP_shape_iff {Op Res : Type} {H : History P Unit Op Res} (hH : WellFormed H)
    (p : P) :
    ((∃ M, restrictP H p = seqHist M) ↔ (opsOf H p ()).length = (ressOf H p ()).length) ∧
    ((∃ M o, restrictP H p = seqHist M ++ [.inv p () o]) ↔
      (opsOf H p ()).length = (ressOf H p ()).length + 1) := by
  obtain ⟨M, -, h | ⟨x, o, h⟩⟩ := hH.restrictP_eq p
  · have h1 : (opsOf H p ()).length = cnt M p () := by
      rw [opsOf_eq_restrictP, h, length_opsOf_seqHist]
    have h2 : (ressOf H p ()).length = cnt M p () := by
      rw [ressOf_eq_restrictP, h, length_ressOf_seqHist]
    refine ⟨⟨fun _ => by omega, fun _ => ⟨M, h⟩⟩, ⟨?_, fun _ => by omega⟩⟩
    rintro ⟨M', o', h'⟩; rw [h] at h'; exact absurd h' (seqHist_ne_concat_inv _ _ _ _ _)
  · have h1 : (opsOf H p ()).length = cnt M p () + 1 := by
      rw [opsOf_eq_restrictP, h]; simp [length_opsOf_seqHist]
    have h2 : (ressOf H p ()).length = cnt M p () := by
      rw [ressOf_eq_restrictP, h]; simp [length_ressOf_seqHist]
    refine ⟨⟨?_, fun _ => by omega⟩, ⟨fun _ => by omega, fun _ => ⟨M, o, h⟩⟩⟩
    rintro ⟨M', h'⟩; rw [h] at h'; exact absurd h'.symm (seqHist_ne_concat_inv _ _ _ _ _)

lemma wellFormed_concat_iff {Op Res : Type} {H : History P Unit Op Res}
    {e : Event P Unit Op Res} : WellFormed (H ++ [e]) ↔ WellFormed H ∧ StepOK H e := by
  constructor
  · intro h
    have hH := h.of_concat
    refine ⟨hH, ?_⟩
    cases e with
    | inv p x o =>
      exact (restrictP_shape_iff hH p).1.1 (wellFormed_concat_inv.1 h).2
    | res p x r =>
      obtain ⟨M, o, hM⟩ := (wellFormed_concat_res.1 h).2
      exact (restrictP_shape_iff hH p).2.1 ⟨M, o, hM⟩
  · rintro ⟨hH, he⟩
    cases e with
    | inv p x o => exact wellFormed_concat_inv.2 ⟨hH, (restrictP_shape_iff hH p).1.2 he⟩
    | res p x r =>
      obtain ⟨M, o, hM⟩ := (restrictP_shape_iff hH p).2.2 he
      exact wellFormed_concat_res.2 ⟨hH, M, o, hM⟩

/-- Well-formedness of a single-object history, event by event (as in
`SharedMemory.WellFormed`). -/
lemma wellFormed_iff_splits {Op Res : Type} {H : History P Unit Op Res} :
    WellFormed H ↔ ∀ β e γ, H = β ++ e :: γ → StepOK β e := by
  induction H using List.reverseRecOn with
  | nil => exact ⟨fun _ β e γ h => by simp at h, fun _ => wellFormed_nil⟩
  | append_singleton H e ih =>
    rw [forall_split_concat, ← ih]
    exact ⟨fun h => (wellFormed_concat_iff.1 h), fun h => wellFormed_concat_iff.2 h⟩

/-- `SharedMemory.WellFormed` is `WellFormed` of the history. -/
theorem wellFormed_toHist_iff (α : List (Label P A)) :
    WellFormed (toHist α) ↔ SharedMemory.WellFormed α := by
  rw [wellFormed_iff_splits]
  constructor
  · intro h β ℓ γ hα p
    subst hα
    have h' := fun e (he : labelEvents ℓ = [e]) => h (toHist β) e (toHist γ) (by simp [he])
    cases ℓ with
    | inv q o =>
      have := h' _ rfl
      simp only [StepOK, opsOf_toHist, ressOf_toHist] at this
      refine ⟨fun hq => ?_, fun hq => by simp at hq⟩
      have : q = p := by by_contra hne; simp [hne] at hq
      subst this; assumption
    | ret q r =>
      have := h' _ rfl
      simp only [StepOK, opsOf_toHist, ressOf_toHist] at this
      refine ⟨fun hq => by simp at hq, fun hq => ?_⟩
      have : q = p := by by_contra hne; simp [hne] at hq
      subst this; assumption
    | tau q => simp
  · intro h β' e γ' hH
    obtain ⟨β, ℓ, γ, rfl, rfl, hℓ, rfl⟩ := toHist_eq_append_cons hH
    cases ℓ with
    | inv q o =>
      simp only [labelEvents, List.cons.injEq, and_true] at hℓ; subst hℓ
      simpa [StepOK] using (h β _ γ rfl q).1 (by simp)
    | ret q r =>
      simp only [labelEvents, List.cons.injEq, and_true] at hℓ; subst hℓ
      simpa [StepOK] using (h β _ γ rfl q).2 (by simp)
    | tau q => simp [labelEvents] at hℓ

/-! ### Canonical identities -/

/-- A list of operation instances of `SharedMemory` is *canonical* if, for every process `p`,
its instances of `p` are `(p, 0), (p, 1), …` in this order. -/
def Canon (I : List (SharedMemory.OpId P)) : Prop :=
  ∀ p, I.filter (fun x => x.1 = p) =
    (List.range (I.filter (fun x => x.1 = p)).length).map (fun j => (p, j))

lemma Canon.of_concat {I : List (SharedMemory.OpId P)} {a : SharedMemory.OpId P}
    (h : Canon (I ++ [a])) : Canon I ∧ a.2 = (I.filter (fun x => x.1 = a.1)).length := by
  have key : ∀ p, I.filter (fun x => x.1 = p) =
      (List.range (I.filter (fun x => x.1 = p)).length).map (fun j => (p, j)) ∧
      (a.1 = p → a.2 = (I.filter (fun x => x.1 = p)).length) := by
    intro p
    have := h p
    rw [List.filter_append] at this
    by_cases hp : a.1 = p
    · simp only [List.filter_cons, hp, decide_true, List.filter_nil, ite_true,
        List.length_append, List.length_singleton, List.range_succ, List.map_append,
        List.map_singleton] at this
      obtain ⟨h1, h2⟩ := List.append_inj' this rfl
      simp only [List.cons.injEq, and_true] at h2
      exact ⟨h1, fun _ => by rw [h2]⟩
    · simp only [List.filter_cons, hp, decide_false, List.filter_nil] at this
      exact ⟨by simpa using this, fun h => absurd h hp⟩
  exact ⟨fun p => (key p).1, (key a.1).2 rfl⟩

lemma cnt_eq_of_map {Op Res : Type} {M : List (OpRec P Unit Op Res)}
    {I : List (SharedMemory.OpId P)} (h : M.map (·.p) = I.map (·.1)) (p : P) :
    cnt M p () = (I.filter (fun x => x.1 = p)).length := by
  rw [← List.countP_eq_length_filter]
  have h1 : I.countP (fun x => decide (x.1 = p)) =
      (I.map (·.1)).countP (fun q => decide (q = p)) := by
    rw [List.countP_map]; rfl
  have h2 : M.countP (fun e => decide (e.p = p)) =
      (M.map (·.p)).countP (fun q => decide (q = p)) := by
    rw [List.countP_map]; rfl
  rw [h1, ← h, ← h2]
  simp [cnt]

/-- Records whose processes follow a canonical list of instances get exactly these
identities. -/
lemma idsOf_eq_of_canon {Op Res : Type} (I : List (SharedMemory.OpId P)) (hI : Canon I)
    (M : List (OpRec P Unit Op Res)) (hM : M.map (·.p) = I.map (·.1)) :
    idsOf M = I.map cid := by
  induction I using List.reverseRecOn generalizing M with
  | nil => simp at hM; simp [hM]
  | append_singleton I a ih =>
    obtain ⟨hI', ha⟩ := hI.of_concat
    rcases List.eq_nil_or_concat M with rfl | ⟨M₀, e, rfl⟩
    · simp at hM
    · simp only [List.concat_eq_append, List.map_append, List.map_singleton] at hM
      obtain ⟨h1, h2⟩ := List.append_inj' hM rfl
      simp only [List.cons.injEq, and_true] at h2
      rw [List.concat_eq_append, idsOf_concat, ih hI' M₀ h1, List.map_append, List.map_singleton,
        cnt_eq_of_map h1, h2, ← ha]
      rfl

/-! ### From `SharedMemory.IsLinearization` to linearization lists -/

/-- The records of a linearization in the sense of `SharedMemory.IsLinearization`, with the
responses computed by running `A`. -/
def recsOf (A : ObjSpec) : A.State → List (SharedMemory.OpId P × A.Op) →
    List (OpRec P Unit A.Op A.Resp)
  | _, [] => []
  | q, (x, o) :: L => ⟨x.1, (), o, (A.δ q o).2⟩ :: recsOf A (A.δ q o).1 L

omit [DecidableEq P] in
lemma runOK_recsOf (q : A.State) (L : List (SharedMemory.OpId P × A.Op)) :
    runOK A.δ q (recsOf A q L) := by
  induction L generalizing q with
  | nil => trivial
  | cons y L ih => obtain ⟨x, o⟩ := y; exact ⟨rfl, ih _⟩

omit [DecidableEq P] in
lemma map_p_recsOf (q : A.State) (L : List (SharedMemory.OpId P × A.Op)) :
    (recsOf A q L).map (·.p) = L.map (·.1.1) := by
  induction L generalizing q with
  | nil => rfl
  | cons y L ih => obtain ⟨x, o⟩ := y; simp [recsOf, ih]

lemma mem_zip_recsOf {α : List (Label P A)} {q : A.State}
    {L : List (SharedMemory.OpId P × A.Op)} (h : SharedMemory.SeqOK α q L)
    {y : SharedMemory.OpId P × A.Op} {e : OpRec P Unit A.Op A.Resp}
    (hye : (y, e) ∈ L.zip (recsOf A q L)) :
    e.o = y.2 ∧ ∀ r, SharedMemory.respOf α y.1 = some r → e.r = r := by
  induction L generalizing q with
  | nil => simp [recsOf] at hye
  | cons z L ih =>
    obtain ⟨x, o⟩ := z
    simp only [recsOf, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hye
    rcases hye with ⟨rfl, rfl⟩ | hye
    · exact ⟨rfl, fun r hr => h.1 r hr⟩
    · exact ih h.2 hye

/-- A linearization in the sense of `SharedMemory.IsLinearization` gives a linearization list
(amended definition). -/
theorem isLinA_of_isLinearization {α : List (Label P A)}
    (hα : SharedMemory.WellFormed α) {L : List (SharedMemory.OpId P × A.Op)}
    (hL : SharedMemory.IsLinearization α L) :
    IsLinA (specOf A) (toHist α) (recsOf A A.init L) := by
  have hwf := (wellFormed_toHist_iff α).2 hα
  have hids : idsOf (recsOf A A.init L) = (L.map Prod.fst).map cid :=
    idsOf_eq_of_canon _ (fun p => hL.procIds_eq hα p) _ (by rw [map_p_recsOf, List.map_map]; rfl)
  refine IsLinA.mk' hwf ?_ ?_ ?_ ?_
  · intro a e hae
    rw [hids, List.map_map, List.zip_map_left] at hae
    obtain ⟨⟨y, e'⟩, hy, he⟩ := List.mem_map.1 hae
    simp only [Prod.map, Function.comp_apply, id, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨ho, hr⟩ := mem_zip_recsOf hL.seq hy
    have hyL : y ∈ L := (List.of_mem_zip hy).1
    refine ⟨?_, fun hc => ?_⟩
    · rw [opOf_toHist, uid_cid, hL.op_eq y hyL, ho]
    · obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.1 (completed_iff_resOf.1 hc)
      rw [resOf_toHist, uid_cid] at hr' ⊢
      rw [hr', hr r hr']
  · intro a hc
    rw [hids]
    have := hL.complete _ ((completed_toHist _ _).1 hc)
    simpa using List.mem_map_of_mem (f := cid) this
  · rw [legal_seqHist_iff]
    intro x
    rw [List.filter_eq_self.2 (by simp)]
    exact seqHist_mem_detSpec.2 (runOK_recsOf _ _)
  · intro a b hab hb
    rw [hids] at hb ⊢
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    have := hL.realtime (uid a) b' ((precedes_toHist _ _ _).1 hab) hb'
    simpa using this.map cid

/-! ### From linearization lists to `SharedMemory.IsLinearization` -/

lemma seqOK_of_runOK {α : List (Label P A)} (Z : List (OpId P Unit × OpRec P Unit A.Op A.Resp))
    (q : A.State)
    (hZ : ∀ ae ∈ Z, Completed (toHist α) ae.1 → resOf (toHist α) ae.1 = some ae.2.r)
    (h : runOK A.δ q (Z.map Prod.snd)) :
    SharedMemory.SeqOK α q (Z.map fun ae => (uid ae.1, ae.2.o)) := by
  induction Z generalizing q with
  | nil => trivial
  | cons ae Z ih =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun r hr => ?_, ih _ (fun b hb => hZ b (List.mem_cons_of_mem _ hb)) h2⟩
    have hr' : resOf (toHist α) ae.1 = some r := by rw [resOf_toHist]; exact hr
    have := hZ ae (by simp) (Completed.of_resOf hr')
    rw [hr', Option.some.injEq] at this
    rw [this]; exact h1

/-- The linearization (in the sense of `SharedMemory.IsLinearization`) of a linearization
list. -/
def toCslibLin (M : List (OpRec P Unit A.Op A.Resp)) : List (SharedMemory.OpId P × A.Op) :=
  ((idsOf M).zip M).map fun ae => (uid ae.1, ae.2.o)

lemma map_fst_toCslibLin (M : List (OpRec P Unit A.Op A.Resp)) :
    (toCslibLin M).map Prod.fst = (idsOf M).map uid := by
  rw [toCslibLin, List.map_map]
  have : ((idsOf M).zip M).map (Prod.fst ∘ fun ae => (uid ae.1, ae.2.o)) =
      (((idsOf M).zip M).map Prod.fst).map uid := by rw [List.map_map]; rfl
  rw [this, List.map_fst_zip (by simp)]

/-- A linearization list (amended definition) gives a linearization in the sense of
`SharedMemory.IsLinearization`. -/
theorem isLinearization_of_isLinA {α : List (Label P A)} {M : List (OpRec P Unit A.Op A.Resp)}
    (hM : IsLinA (specOf A) (toHist α) M) :
    SharedMemory.IsLinearization α (toCslibLin M) := by
  have hfst := map_fst_toCslibLin M
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfst]; exact (nodup_idsOf M).map uid_injective
  · intro y hy
    obtain ⟨⟨a, e⟩, hae, rfl⟩ := List.mem_map.1 hy
    have := (hM.recs a e hae).1
    rwa [opOf_toHist] at this
  · intro a hc
    rw [hfst]
    have := hM.complete (cid a) ((completed_toHist _ _).2 (by simpa using hc))
    simpa using List.mem_map_of_mem (f := uid) this
  · intro a b hab hb
    rw [hfst] at hb ⊢
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    have := hM.realtime (cid a) b' (by simpa [precedes_toHist] using hab) hb'
    simpa using this.map uid
  · have hlegal := (legal_seqHist_iff _ _).1 hM.legal ()
    rw [List.filter_eq_self.2 (by simp)] at hlegal
    have hrun : runOK A.δ A.init M := seqHist_mem_detSpec.1 hlegal
    refine seqOK_of_runOK _ _ (fun ae hae hc => (hM.recs ae.1 ae.2 hae).2 hc) ?_
    rwa [List.map_snd_zip (by simp)]

/-! ### Main results -/

/-- **`SharedMemory.IsLinearization` is the amended definition** (Definition 4.1 of
Sela–Herlihy–Petrank, list form): for a well-formed execution, a linearization in the sense of
`SharedMemory.IsLinearization` exists iff a linearization list in the sense of `IsLinA` exists
for its history. -/
theorem isLinearization_iff_isLinA {α : List (Label P A)}
    (hα : SharedMemory.WellFormed α) :
    (∃ L, SharedMemory.IsLinearization α L) ↔ ∃ M, IsLinA (specOf A) (toHist α) M :=
  ⟨fun ⟨_, hL⟩ => ⟨_, isLinA_of_isLinearization hα hL⟩,
    fun ⟨_, hM⟩ => ⟨_, isLinearization_of_isLinA hM⟩⟩

/-- A well-formed execution is linearizable in the sense of `SharedMemory.IsLinearization` iff
its history is linearizable by the amended definition (Definition 4.1 of
Sela–Herlihy–Petrank). -/
theorem cslib_linearizable_iff {α : List (Label P A)} (hα : SharedMemory.WellFormed α) :
    (∃ L, SharedMemory.IsLinearization α L) ↔ Linearizable (specOf A) (toHist α) := by
  rw [isLinearization_iff_isLinA hα, linearizable_iff]
  exact ⟨fun h => ⟨(wellFormed_toHist_iff α).2 hα, h⟩, fun h => h.2⟩

/-- The amended definition (Definition 4.1 of Sela–Herlihy–Petrank) of linearizability of a
well-formed single-object history is linearizability in the sense of
`SharedMemory.IsLinearization`. -/
theorem linearizable_iff_cslib (H : History P Unit A.Op A.Resp) (hH : WellFormed H) :
    Linearizable (specOf A) H ↔
      ∃ L, SharedMemory.IsLinearization (ofHist H : List (Label P A)) L := by
  have hα : SharedMemory.WellFormed (ofHist H : List (Label P A)) :=
    (wellFormed_toHist_iff _).1 (by simpa using hH)
  have := cslib_linearizable_iff hα
  rw [toHist_ofHist] at this
  exact this.symm

end Cslib.SharedMemory.HerlihyWing
