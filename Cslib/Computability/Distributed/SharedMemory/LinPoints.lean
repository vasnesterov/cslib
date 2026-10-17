/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Linearization

/-!
# Building linearizations incrementally (linearization points)

Lemmas to maintain a linearization `L` of a growing execution `α`:

* `IsLinearization.append_inv` / `append_tau`: invocations and internal steps keep `L` a
  linearization;
* `IsLinearization.push`: a pending, not yet linearized operation can be appended to `L` (its
  *linearization point*);
* `IsLinearization.append_ret`: a response keeps `L` a linearization if the returning operation
  is already in `L` and the specification gives it this response at its position in `L`.

## Responses assigned by a sequential history

`ObjSpec.respIn A q L x` is the response that the sequential specification `A` gives to the entry
with key `x` (its first occurrence) when the sequential history `L` is run from state `q`
(`none` if `x` does not occur). Keys are arbitrary (operation instances `OpId P` for
linearizations; other models use e.g. `ℕ`). Main lemmas: `respIn_append_of_mem`,
`respIn_append_of_not_mem`, `respIn_isSome_iff`, `exists_split_of_respIn_eq_some`,
`respIn_insert`, `respIn_insert_self`, `respIn_append_const` (with `runOps_map_snd_const`); for
linearizations: `SeqOK.respIn_eq`, `seqOK_of_respIn`,
`IsLinearization.respIn_eq` (a completed instance gets its actual response) and
`IsLinearization.append_ret_of_respIn` (a response is legal if the linearization assigns it).

`ObjSpec.respIn` is a reducible spelling of the recursive definition `linRespFrom A x q L`, so
lemmas about either apply to both. `linResp L x` is the response in a linearization (from the
initial state); use the `respIn_*` lemmas for both.

## Building linearizations

* `isLinearization_nil`, `IsLinearization.push_list` (linearizing several pending instances);
* `IsLinearization.insert`: a *retroactive* linearization point: a pending operation that does
  not change the state at the chosen position can be inserted into the middle of a
  linearization, provided no operation after the insertion point precedes it in real time;
* `split_insert'`, `split_insert`, `split_cons_insert`: how a split `L = L₁ ++ L₂` survives such
  an insertion.
-/

@[expose] public section

namespace Cslib.SharedMemory

open List

variable {P : Type} {A : ObjSpec} [DecidableEq P]

/-- `SeqOK` only depends on the responses of the listed instances. -/
lemma seqOK_congr {α α' : List (Label P A)} (q : A.State) (L : List (OpId P × A.Op))
    (h : ∀ y ∈ L, respOf α y.1 = respOf α' y.1) : SeqOK α q L ↔ SeqOK α' q L := by
  induction L generalizing q with
  | nil => simp [SeqOK]
  | cons y L ih =>
    obtain ⟨x, o⟩ := y
    simp only [SeqOK]
    rw [h (x, o) (by simp), ih _ (fun y hy => h y (by simp [hy]))]

namespace IsLinearization

variable {α : List (Label P A)} {L : List (OpId P × A.Op)}

lemma mem_invoked (hL : IsLinearization α L) {x : OpId P} (hx : x ∈ L.map Prod.fst) :
    Invoked α x := hL.invoked_of_mem hx

/-- Appending a label that does not change the history of instances in `L` and creates no new
completed instance. -/
lemma append_of_hist {ℓ : Label P A} (hL : IsLinearization α L)
    (hops : ∀ x, Invoked α x → opOf (α ++ [ℓ]) x = opOf α x)
    (hresp : ∀ x, respOf (α ++ [ℓ]) x = respOf α x) :
    IsLinearization (α ++ [ℓ]) L where
  nodup := hL.nodup
  op_eq y hy := by rw [hops _ (hL.mem_invoked (mem_map.2 ⟨y, hy, rfl⟩))]; exact hL.op_eq y hy
  complete a ha := by
    apply hL.complete
    rw [completed_iff_respOf, ← hresp a]; exact completed_iff_respOf.1 ha
  realtime a b hab hb := hL.realtime a b (hab.of_append_of_invoked (hL.mem_invoked hb)) hb
  seq := (seqOK_congr _ _ (fun y _ => hresp y.1)).2 hL.seq

lemma append_inv (hL : IsLinearization α L) (p : P) (o : A.Op) :
    IsLinearization (α ++ [.inv p o]) L :=
  hL.append_of_hist (fun _ hx => opOf_append_of_invoked hx)
    (fun x => by simp [respOf, respsOf_append])

lemma append_tau (hL : IsLinearization α L) (p : P) :
    IsLinearization (α ++ [.tau p]) L :=
  hL.append_of_hist (fun _ hx => opOf_append_of_invoked hx)
    (fun x => by simp [respOf, respsOf_append])

/-- A linearization point: a pending instance not yet in `L` can be appended to `L`. -/
lemma push (hL : IsLinearization α L) {x : OpId P} {o : A.Op} (hx : opOf α x = some o)
    (hxL : x ∉ L.map Prod.fst) (hxc : ¬ Completed α x) :
    IsLinearization α (L ++ [(x, o)]) where
  nodup := by
    rw [map_append, nodup_append]
    exact ⟨hL.nodup, by simp, by
      simp only [map_cons, map_nil, mem_singleton]; rintro a ha b rfl rfl; exact hxL ha⟩
  op_eq y hy := by
    rcases mem_append.1 hy with hy | hy
    · exact hL.op_eq y hy
    · simp only [mem_cons, not_mem_nil, or_false] at hy; subst hy; exact hx
  complete a ha := by rw [map_append]; exact mem_append_left _ (hL.complete a ha)
  realtime a b hab hb := by
    rw [map_append] at hb ⊢
    rcases mem_append.1 hb with hb | hb
    · exact (hL.realtime a b hab hb).trans (sublist_append_left _ _)
    · simp only [map_cons, map_nil, mem_cons, not_mem_nil, or_false] at hb; subst hb
      have ha := hL.complete a hab.completed
      exact sublist_pair_iff.2 ⟨L.map Prod.fst, [(b, o)].map Prod.fst, rfl, ha, by simp⟩
  seq := by
    rw [seqOK_append]
    refine ⟨hL.seq, ?_, trivial⟩
    intro r hr
    exact absurd (completed_iff_respOf.2 (by rw [hr]; rfl)) hxc

/-- A response: the returning instance `(p, k)` (`k` = number of earlier responses of `p`) must
already be linearized, and the specification must give it response `r` at its position. -/
lemma append_ret (hL : IsLinearization α L) {p : P} {r : A.Resp}
    (L₁ L₂ : List (OpId P × A.Op)) (o : A.Op)
    (hsplit : L = L₁ ++ ((p, (respsOf α p).length), o) :: L₂)
    (hr : (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).2 = r) :
    IsLinearization (α ++ [.ret p r]) L := by
  set x : OpId P := (p, (respsOf α p).length) with hx
  have hnd := hL.nodup
  rw [hsplit, map_append, map_cons, nodup_append] at hnd
  have hx1 : x ∉ L₁.map Prod.fst := fun h => hnd.2.2 x h x (by simp) rfl
  have hx2 : x ∉ L₂.map Prod.fst := (nodup_cons.1 hnd.2.1).1
  have hxL : x ∈ L.map Prod.fst := by rw [hsplit]; simp
  have hresp : ∀ y, y ≠ x → respOf (α ++ [.ret p r]) y = respOf α y := by
    intro y hy; rw [respOf_append_ret, ite_eq_right hy]
  have hopsx : ∀ y, opOf (α ++ [.ret p r]) y = opOf α y := by
    intro y; simp [opOf, opsOf_append]
  refine ⟨hL.nodup, fun y hy => by rw [hopsx]; exact hL.op_eq y hy, ?_, ?_, ?_⟩
  · intro a ha
    by_cases hax : a = x
    · rw [hax]; exact hxL
    · apply hL.complete
      rw [completed_iff_respOf, ← hresp a hax]; exact completed_iff_respOf.1 ha
  · intro a b hab hb
    exact hL.realtime a b (hab.of_append_of_invoked (hL.mem_invoked hb)) hb
  · have hseq := hL.seq
    rw [hsplit, seqOK_append] at hseq ⊢
    have hc1 : ∀ y ∈ L₁, respOf (α ++ [.ret p r]) y.1 = respOf α y.1 :=
      fun y hy => hresp _ (fun h => hx1 (h ▸ mem_map.2 ⟨y, hy, rfl⟩))
    have hc2 : ∀ y ∈ L₂, respOf (α ++ [.ret p r]) y.1 = respOf α y.1 :=
      fun y hy => hresp _ (fun h => hx2 (h ▸ mem_map.2 ⟨y, hy, rfl⟩))
    refine ⟨(seqOK_congr _ _ hc1).2 hseq.1, ?_, (seqOK_congr _ _ hc2).2 hseq.2.2⟩
    intro r' hr'
    rw [respOf_append_ret, ite_eq_left rfl] at hr'
    cases hr'; exact hr

end IsLinearization

end Cslib.SharedMemory

namespace Cslib.SharedMemory

open List

/-! ## Responses in sequential histories -/

/-- The response that the sequential specification `A` gives to the (first) entry with key `x`
when the sequential history `L` is run from state `q` (`none` if `x` does not occur in `L`).
Use it through `ObjSpec.respIn A q L x`, which has the API lemmas. -/
def linRespFrom (A : ObjSpec) {K : Type} [DecidableEq K] (x : K) :
    A.State → List (K × A.Op) → Option A.Resp
  | _, [] => none
  | q, (y, o) :: L => if y = x then some (A.δ q o).2 else linRespFrom A x (A.δ q o).1 L

namespace ObjSpec

/-- The response that `A` gives to the (first) entry with key `x` when the sequential history `L`
is run from state `q`; `none` if `x` does not occur in `L`. This is `linRespFrom A x q L`. -/
abbrev respIn (A : ObjSpec) {K : Type} [DecidableEq K] (q : A.State) (L : List (K × A.Op))
    (x : K) : Option A.Resp :=
  linRespFrom A x q L

variable {A : ObjSpec} {K : Type} [DecidableEq K] {q : A.State} {L M : List (K × A.Op)} {x : K}

@[simp] lemma respIn_nil (q : A.State) (x : K) : A.respIn q [] x = none := rfl

lemma respIn_cons (q : A.State) (y : K) (o : A.Op) (L : List (K × A.Op)) (x : K) :
    A.respIn q ((y, o) :: L) x =
      if y = x then some (A.δ q o).2 else A.respIn (A.δ q o).1 L x := rfl

@[simp] lemma respIn_cons_self (q : A.State) (x : K) (o : A.Op) (L : List (K × A.Op)) :
    A.respIn q ((x, o) :: L) x = some (A.δ q o).2 := by
  simp [respIn_cons]

@[simp] lemma respIn_cons_of_ne (q : A.State) {y : K} (o : A.Op) (L : List (K × A.Op))
    (h : y ≠ x) : A.respIn q ((y, o) :: L) x = A.respIn (A.δ q o).1 L x := by
  simp [respIn_cons, h]

lemma respIn_singleton (q : A.State) (y : K) (o : A.Op) (x : K) :
    A.respIn q [(y, o)] x = if y = x then some (A.δ q o).2 else none := by
  simp [respIn_cons]

lemma respIn_isSome_iff : (A.respIn q L x).isSome ↔ x ∈ L.map Prod.fst := by
  induction L generalizing q with
  | nil => simp
  | cons y L ih =>
    obtain ⟨y, o⟩ := y
    by_cases h : y = x
    · subst h; simp
    · simp [h, ih, Ne.symm h]

lemma respIn_eq_none_iff : A.respIn q L x = none ↔ x ∉ L.map Prod.fst := by
  rw [← respIn_isSome_iff (A := A) (q := q)]; simp

lemma respIn_eq_none (hx : x ∉ L.map Prod.fst) : A.respIn q L x = none :=
  respIn_eq_none_iff.2 hx

lemma mem_of_respIn_eq_some {r : A.Resp} (h : A.respIn q L x = some r) : x ∈ L.map Prod.fst :=
  respIn_isSome_iff.1 (by rw [h]; rfl)

lemma respIn_append (q : A.State) (L M : List (K × A.Op)) (x : K) :
    A.respIn q (L ++ M) x =
      (A.respIn q L x).or (A.respIn (A.runOps q (L.map Prod.snd)) M x) := by
  induction L generalizing q with
  | nil => simp
  | cons y L ih =>
    obtain ⟨y, o⟩ := y
    by_cases h : y = x
    · subst h; simp
    · simp [h, ih]

lemma respIn_append_of_mem (hx : x ∈ L.map Prod.fst) (M : List (K × A.Op)) :
    A.respIn q (L ++ M) x = A.respIn q L x := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 ((respIn_isSome_iff (q := q)).2 hx)
  simp [respIn_append, hr]

lemma respIn_append_of_not_mem (hx : x ∉ L.map Prod.fst) (M : List (K × A.Op)) :
    A.respIn q (L ++ M) x = A.respIn (A.runOps q (L.map Prod.snd)) M x := by
  simp [respIn_append, respIn_eq_none hx]

lemma respIn_append_of_not_mem_right (hx : x ∉ M.map Prod.fst) :
    A.respIn q (L ++ M) x = A.respIn q L x := by
  by_cases hL : x ∈ L.map Prod.fst
  · exact respIn_append_of_mem hL M
  · rw [respIn_eq_none hL, respIn_eq_none]
    simp only [map_append, mem_append, not_or]; exact ⟨hL, hx⟩

lemma respIn_append_of_eq_some {r : A.Resp} (h : A.respIn q L x = some r)
    (M : List (K × A.Op)) : A.respIn q (L ++ M) x = some r := by
  rw [respIn_append_of_mem (mem_of_respIn_eq_some h), h]

lemma respIn_concat_self (hx : x ∉ L.map Prod.fst) (o : A.Op) :
    A.respIn q (L ++ [(x, o)]) x = some (A.δ (A.runOps q (L.map Prod.snd)) o).2 := by
  simp [respIn_append_of_not_mem hx]

/-- Splitting a sequential history at an entry with a known response. -/
lemma exists_split_of_respIn_eq_some {r : A.Resp} (h : A.respIn q L x = some r) :
    ∃ L₁ L₂ o, L = L₁ ++ (x, o) :: L₂ ∧ (A.δ (A.runOps q (L₁.map Prod.snd)) o).2 = r := by
  induction L generalizing q with
  | nil => simp at h
  | cons y L ih =>
    obtain ⟨y, o⟩ := y
    by_cases hy : y = x
    · subst hy; simp only [respIn_cons_self, Option.some.injEq] at h
      exact ⟨[], L, o, by simp, by simpa using h⟩
    · rw [respIn_cons_of_ne _ _ _ hy] at h
      obtain ⟨L₁, L₂, o', hs, hr⟩ := ih h
      exact ⟨(y, o) :: L₁, L₂, o', by simp [hs], by simpa using hr⟩

/-- The response of an entry at a known position of a duplicate-free history. -/
lemma respIn_of_split {L₁ L₂ : List (K × A.Op)} {o : A.Op} (hnd : (L.map Prod.fst).Nodup)
    (hL : L = L₁ ++ (x, o) :: L₂) :
    A.respIn q L x = some (A.δ (A.runOps q (L₁.map Prod.snd)) o).2 := by
  subst hL
  have hx : x ∉ L₁.map Prod.fst := by
    simp only [map_append, map_cons] at hnd
    exact fun h => (nodup_append.1 hnd).2.2 _ h _ (by simp) rfl
  simp [respIn_append_of_not_mem hx]

/-- Inserting an operation that does not change the state at its position does not change the
responses of the other entries. -/
lemma respIn_insert (q : A.State) (S₁ S₂ : List (K × A.Op)) {y : K} {o : A.Op}
    (hneu : (A.δ (A.runOps q (S₁.map Prod.snd)) o).1 = A.runOps q (S₁.map Prod.snd))
    (hxy : y ≠ x) : A.respIn q (S₁ ++ (y, o) :: S₂) x = A.respIn q (S₁ ++ S₂) x := by
  by_cases hx : x ∈ S₁.map Prod.fst
  · rw [respIn_append_of_mem hx, respIn_append_of_mem hx]
  · rw [respIn_append_of_not_mem hx, respIn_append_of_not_mem hx, respIn_cons_of_ne _ _ _ hxy,
      hneu]

lemma respIn_insert_self (q : A.State) (S₁ S₂ : List (K × A.Op)) {y : K} (o : A.Op)
    (hy : y ∉ S₁.map Prod.fst) :
    A.respIn q (S₁ ++ (y, o) :: S₂) y = some (A.δ (A.runOps q (S₁.map Prod.snd)) o).2 := by
  simp [respIn_append_of_not_mem hy]

omit [DecidableEq K] in
/-- Operations that keep the state `q` (all with the same response `r`) leave it unchanged when
run in sequence. -/
lemma runOps_map_snd_const (r : A.Resp) {l : List (K × A.Op)} (hl : ∀ y ∈ l, A.δ q y.2 = (q, r)) :
    A.runOps q (l.map Prod.snd) = q := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [List.map_cons, ObjSpec.runOps_cons, hl y (by simp)]
    exact ih (fun z hz => hl z (by simp [hz]))

/-- Entries whose operations keep the state `q` and return `r` all get the response `r`. -/
lemma respIn_append_const (r : A.Resp) {l : List (K × A.Op)} (hl : ∀ y ∈ l, A.δ q y.2 = (q, r))
    (hx : x ∈ l.map Prod.fst) (M : List (K × A.Op)) : A.respIn q (l ++ M) x = some r := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    obtain ⟨y, o⟩ := y
    have hy := hl (y, o) (by simp)
    by_cases h : y = x
    · subst h; simp [hy]
    · simp only [cons_append, respIn_cons_of_ne _ _ _ h, hy]
      simp only [map_cons, mem_cons] at hx
      exact ih (fun z hz => hl z (by simp [hz])) (hx.resolve_left (Ne.symm h))

end ObjSpec

/-! ## Responses in linearizations -/

section Lin

variable {P : Type} {A : ObjSpec} [DecidableEq P]

/-- In a legal sequential history, a completed instance gets its actual response. -/
lemma SeqOK.respIn_eq {α : List (Label P A)} {q : A.State} {L : List (OpId P × A.Op)}
    (hL : SeqOK α q L) {x : OpId P} {r : A.Resp} (hr : respOf α x = some r)
    (hx : x ∈ L.map Prod.fst) : A.respIn q L x = some r := by
  induction L generalizing q with
  | nil => simp at hx
  | cons y L ih =>
    obtain ⟨y, o⟩ := y
    obtain ⟨h1, h2⟩ := hL
    by_cases hy : y = x
    · subst hy; simp [h1 r hr]
    · rw [ObjSpec.respIn_cons_of_ne _ _ _ hy]
      simp only [map_cons, mem_cons] at hx
      exact ih h2 (hx.resolve_left (Ne.symm hy))

/-- A duplicate-free sequential history is legal if it assigns to every completed instance its
actual response. -/
lemma seqOK_of_respIn {α : List (Label P A)} {q : A.State} {L : List (OpId P × A.Op)}
    (hnd : (L.map Prod.fst).Nodup)
    (h : ∀ x r, x ∈ L.map Prod.fst → respOf α x = some r → A.respIn q L x = some r) :
    SeqOK α q L := by
  induction L generalizing q with
  | nil => trivial
  | cons y L ih =>
    obtain ⟨y, o⟩ := y
    simp only [map_cons, nodup_cons] at hnd
    refine ⟨fun r hr => ?_, ih hnd.2 fun x r hx hr => ?_⟩
    · simpa using h y r (by simp) hr
    · have hne : y ≠ x := fun e => hnd.1 (e ▸ hx)
      simpa [hne] using h x r (by simp [hx]) hr

/-- A completed instance gets its actual response in every linearization. -/
lemma IsLinearization.respIn_eq {α : List (Label P A)} {L : List (OpId P × A.Op)}
    (hL : IsLinearization α L) {x : OpId P} {r : A.Resp} (hr : respOf α x = some r) :
    A.respIn A.init L x = some r :=
  hL.seq.respIn_eq hr (hL.complete x (Completed.of_respOf_eq_some hr))

/-- A response is legal if the linearization assigns it to the returning instance. -/
lemma IsLinearization.append_ret_of_respIn {α : List (Label P A)} {L : List (OpId P × A.Op)}
    (hL : IsLinearization α L) {p : P} {r : A.Resp}
    (hr : A.respIn A.init L (p, (respsOf α p).length) = some r) :
    IsLinearization (α ++ [.ret p r]) L := by
  obtain ⟨L₁, L₂, o, hs, hr'⟩ := ObjSpec.exists_split_of_respIn_eq_some hr
  exact hL.append_ret L₁ L₂ o hs hr'

/-- The empty linearization of the empty execution. -/
lemma isLinearization_nil : IsLinearization ([] : List (Label P A)) [] :=
  ⟨by simp, by simp, fun a ha => by simp [Completed] at ha, fun a b _ hb => by simp at hb,
    trivial⟩

/-- Linearizing several pending instances at once (in the given order). -/
lemma IsLinearization.push_list {α : List (Label P A)} {L : List (OpId P × A.Op)}
    (hL : IsLinearization α L) (M : List (OpId P × A.Op))
    (hM : ∀ y ∈ M, opOf α y.1 = some y.2 ∧ ¬ Completed α y.1)
    (hnd : (M.map Prod.fst).Nodup) (hdisj : ∀ y ∈ M, y.1 ∉ L.map Prod.fst) :
    IsLinearization α (L ++ M) := by
  induction M using List.reverseRecOn with
  | nil => simpa using hL
  | append_singleton M y ih =>
    have ih' := ih (fun z hz => hM z (by simp [hz]))
      (by rw [List.map_append] at hnd; exact (List.nodup_append.1 hnd).1)
      (fun z hz => hdisj z (by simp [hz]))
    rw [← List.append_assoc]
    obtain ⟨h1, h2⟩ := hM y (by simp)
    refine ih'.push h1 ?_ h2
    rw [List.map_append, List.mem_append, not_or]
    refine ⟨hdisj y (by simp), fun hm => ?_⟩
    rw [List.map_append, List.nodup_append] at hnd
    exact hnd.2.2 _ hm _ (by simp) rfl

/-! ### `OpId`-keyed spellings -/

/-- The response that the linearization `L` assigns to the instance `x`. -/
def linResp (L : List (OpId P × A.Op)) (x : OpId P) : Option A.Resp :=
  linRespFrom A x A.init L

/-! ## Retroactive linearization points -/

/-- Retroactive linearization point: insert a pending operation `x` (which does not change the
state reached after `L₁`) between `L₁` and `L₂`, if nothing in `L₂` precedes `x`. -/
lemma IsLinearization.insert {α : List (Label P A)} {L₁ L₂ : List (OpId P × A.Op)}
    (hL : IsLinearization α (L₁ ++ L₂)) {x : OpId P} {o : A.Op} (hx : opOf α x = some o)
    (hxL : x ∉ (L₁ ++ L₂).map Prod.fst) (hxc : ¬ Completed α x)
    (hro : (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).1 = A.runOps A.init (L₁.map Prod.snd))
    (h2 : ∀ y ∈ L₂, ¬ Precedes α y.1 x) : IsLinearization α (L₁ ++ (x, o) :: L₂) where
  nodup := by
    have := hL.nodup
    simp only [map_append, map_cons] at this hxL ⊢
    rw [nodup_middle, nodup_cons]
    exact ⟨hxL, this⟩
  op_eq y hy := by
    simp only [mem_append, mem_cons] at hy
    rcases hy with hy | rfl | hy
    · exact hL.op_eq y (mem_append_left _ hy)
    · exact hx
    · exact hL.op_eq y (mem_append_right _ hy)
  complete a ha := by
    have := hL.complete a ha
    simp only [map_append, map_cons, mem_append, mem_cons] at this ⊢
    tauto
  realtime a b hab hb := by
    have hsub : (L₁ ++ L₂).map Prod.fst <+ (L₁ ++ (x, o) :: L₂).map Prod.fst := by
      simp only [map_append, map_cons]
      exact Sublist.append_left (sublist_cons_self _ _) _
    by_cases hbx : b = x
    · subst hbx
      have ha := hL.complete a hab.completed
      have ha1 : a ∈ L₁.map Prod.fst := by
        simp only [map_append, mem_append] at ha
        rcases ha with ha | ha
        · exact ha
        · obtain ⟨y, hy, rfl⟩ := mem_map.1 ha
          exact absurd hab (h2 y hy)
      rw [sublist_pair_iff]
      exact ⟨L₁.map Prod.fst, (L₂.map Prod.fst).cons b, by simp, ha1, by simp⟩
    · have hb' : b ∈ (L₁ ++ L₂).map Prod.fst := by
        simp only [map_append, map_cons, mem_append, mem_cons] at hb ⊢
        rcases hb with hb | hb | hb
        · exact Or.inl hb
        · exact absurd hb hbx
        · exact Or.inr hb
      exact (hL.realtime a b hab hb').trans hsub
  seq := by
    have hs := hL.seq
    rw [seqOK_append] at hs ⊢
    refine ⟨hs.1, ?_, ?_⟩
    · intro r hr
      exact absurd (completed_iff_respOf.2 (by rw [hr]; rfl)) hxc
    · rw [hro]; exact hs.2

end Lin

/-- A split `L = S₁ ++ S₂` survives the insertion of `z` at another split `L = W₁ ++ W₂`: `z`
lands either in the right part, or in the left part right after `W₁`. -/
lemma split_insert' {X : Type} {S₁ S₂ W₁ W₂ : List X} (h : S₁ ++ S₂ = W₁ ++ W₂) (z : X) :
    ∃ S₁' S₂', W₁ ++ z :: W₂ = S₁' ++ S₂' ∧ (∀ y ∈ S₂', y ∈ S₂ ∨ y = z) ∧
      (∀ y ∈ S₂, y ∈ S₂') ∧ (S₁' = S₁ ∨ ∃ B, S₁ = W₁ ++ B ∧ S₁' = W₁ ++ z :: B) := by
  rcases append_eq_append_iff.1 h with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
  · -- `W₁ = S₁ ++ a'`, `S₂ = a' ++ W₂`
    refine ⟨S₁, a' ++ z :: W₂, by simp, ?_, ?_, Or.inl rfl⟩
    · intro y hy; simp only [mem_append, mem_cons] at hy ⊢; tauto
    · intro y hy; simp only [mem_append, mem_cons] at hy ⊢; tauto
  · -- `S₁ = W₁ ++ c'`, `W₂ = c' ++ S₂`
    exact ⟨W₁ ++ z :: c', S₂, by simp, fun y hy => Or.inl hy, fun y hy => hy,
      Or.inr ⟨c', rfl, rfl⟩⟩

/-- A split `L = S₁ ++ S₂` survives the insertion of `z` at another split `L = W₁ ++ W₂`:
`z` lands either in the left part or in the right part (weaker form of `split_insert'`). -/
lemma split_insert {X : Type} {S₁ S₂ W₁ W₂ : List X} (h : S₁ ++ S₂ = W₁ ++ W₂) (z : X) :
    ∃ S₁' S₂', W₁ ++ z :: W₂ = S₁' ++ S₂' ∧ (∀ y ∈ S₂', y ∈ S₂ ∨ y = z) ∧
      (∀ y ∈ S₂, y ∈ S₂') ∧ (S₁' = S₁ ∨ ∃ A B, S₁ = A ++ B ∧ S₁' = A ++ z :: B) := by
  obtain ⟨S₁', S₂', h1, h2, h3, h4⟩ := split_insert' h z
  exact ⟨S₁', S₂', h1, h2, h3, h4.imp_right fun ⟨B, hB⟩ => ⟨W₁, B, hB⟩⟩

/-- A split around an element, `L = L₁ ++ y :: L₂`, survives the insertion of `z` at another
split `L = W₁ ++ W₂`. -/
lemma split_cons_insert {X : Type} {L₁ L₂ W₁ W₂ : List X} {y : X}
    (h : L₁ ++ y :: L₂ = W₁ ++ W₂) (z : X) :
    ∃ L₁' L₂', W₁ ++ z :: W₂ = L₁' ++ y :: L₂' ∧
      (L₁' = L₁ ∨ ∃ A B, L₁ = A ++ B ∧ L₁' = A ++ z :: B) := by
  rcases append_eq_append_iff.1 h with ⟨a', rfl, h2⟩ | ⟨c', rfl, rfl⟩
  · rcases a' with _ | ⟨y', a'⟩
    · simp only [nil_append] at h2; subst h2
      exact ⟨L₁ ++ [z], L₂, by simp, Or.inr ⟨L₁, [], by simp, rfl⟩⟩
    · simp only [cons_append, cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact ⟨L₁, a' ++ z :: W₂, by simp, Or.inl rfl⟩
  · exact ⟨W₁ ++ z :: c', L₂, by simp, Or.inr ⟨W₁, c', rfl, rfl⟩⟩

end Cslib.SharedMemory
