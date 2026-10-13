/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.LinPoints
public import Mathlib.Data.List.Dedup

/-!
# Locality of amended linearizability

Theorem 5.1 of Sela–Herlihy–Petrank (Theorem 1 of Herlihy–Wing, for the amended definition):
`H` is linearizable (Definition 4.1) iff every object subhistory `H|x` is.

## Main results

* `IsLinA.restrictX`: a linearization of `H` restricts to linearizations of the `H|x`.
* `exists_isLinA_of_restrictX`, `linearizable_of_restrictX`: the "if" direction.
* `locality`: Theorem 5.1.

## Implementation notes

The proof of the "if" direction differs from the acyclicity argument of Sela–Herlihy–Petrank:
for every object `x` pick a linearization `M x` of `H|x` and give each of its operations `a` the
linearization point `runMax H (idsOf (M x)) a` (the running maximum, in `H`, of the invocation
times of the operations of `M x` up to `a`; cf. Claim 1). Linearization points of operations of
different objects never coincide (each is the invocation time of an operation of that object),
so sorting all operations by (point, position in `M x`) yields a single linearization of `H`
(`mergedM`, `isLinA_mergedM`).

## References

* [M. P. Herlihy, J. M. Wing, *Linearizability: A Correctness Condition for Concurrent
  Objects*][HerlihyWing1990]
* [G. Sela, M. Herlihy, E. Petrank, *Brief Announcement: Linearizability: A
  Typo*][SelaHerlihyPetrank2021]
-/

@[expose] public section

namespace Cslib.SharedMemory.HerlihyWing

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

/-! ### Object subhistories -/

lemma restrictP_restrictX (H : History P X Op Res) (p : P) (x : X) :
    restrictP (restrictX H x) p = restrictX (restrictP H p) x := by
  simp only [restrictP, restrictX, List.filter_filter]
  congr 1; funext e; exact Bool.and_comm _ _

lemma wellFormed_restrictX {H : History P X Op Res} (hH : WellFormed H) (x : X) :
    WellFormed (restrictX H x) := by
  intro p
  rw [restrictP_restrictX]
  obtain ⟨M, -, h | ⟨y, o, h⟩⟩ := hH.restrictP_eq p
  · rw [h, restrictX_seqHist]; exact isSeq_seqHist _
  · rw [h, restrictX_append, restrictX_seqHist, restrictX_singleton]
    split_ifs
    · exact ⟨_, Or.inr ⟨p, y, o, rfl⟩⟩
    · simpa using isSeq_seqHist _

lemma completed_restrictX {H : History P X Op Res} {x : X} {a : OpId P X} :
    Completed (restrictX H x) a ↔ a.x = x ∧ Completed H a := by
  by_cases h : a.x = x
  · simp [Completed, h]
  · simp [Completed, Ne.symm h, h]

lemma invoked_restrictX {H : History P X Op Res} {x : X} {a : OpId P X} :
    Invoked (restrictX H x) a ↔ a.x = x ∧ Invoked H a := by
  by_cases h : a.x = x
  · simp [Invoked, h]
  · simp [Invoked, Ne.symm h, h]

lemma opOf_restrictX {H : History P X Op Res} {x : X} {a : OpId P X} (h : a.x = x) :
    opOf (restrictX H x) a = opOf H a := by
  simp [opOf, h]

lemma resOf_restrictX {H : History P X Op Res} {x : X} {a : OpId P X} (h : a.x = x) :
    resOf (restrictX H x) a = resOf H a := by
  simp [resOf, h]

lemma completed_restrictX_of_eq {β : History P X Op Res} {x : X} {a : OpId P X}
    (h : a.x = x) : Completed (restrictX β x) a ↔ Completed β a := by
  rw [completed_restrictX]; simp [h]

lemma invoked_restrictX_of_eq {β : History P X Op Res} {x : X} {a : OpId P X}
    (h : a.x = x) : Invoked (restrictX β x) a ↔ Invoked β a := by
  rw [invoked_restrictX]; simp [h]

/-- Real-time order between operations of `x` is the same in `H` and in `H|x`. -/
lemma precedes_restrictX {H : History P X Op Res} {x : X} {a b : OpId P X} (ha : a.x = x)
    (hb : b.x = x) : Precedes (restrictX H x) a b ↔ Precedes H a b := by
  constructor
  · rintro ⟨β', γ', h, h1, h2⟩
    obtain ⟨β, γ, rfl, rfl, rfl⟩ := List.filter_eq_append_iff.1 h
    exact ⟨β, γ, rfl, (completed_restrictX_of_eq ha).1 h1,
      fun h' => h2 ((invoked_restrictX_of_eq hb).2 h')⟩
  · rintro ⟨β, γ, rfl, h1, h2⟩
    exact ⟨restrictX β x, restrictX γ x, by simp, (completed_restrictX_of_eq ha).2 h1,
      fun h' => h2 ((invoked_restrictX_of_eq hb).1 h')⟩

/-- Identities of a linearization of `H|x` are operations of `x`. -/
lemma IsLinA.obj_eq {spec : SeqSpec P X Op Res} {H : History P X Op Res} {x : X}
    {M : List (OpRec P X Op Res)} (hM : IsLinA spec (restrictX H x) M) {a : OpId P X}
    (ha : a ∈ idsOf M) : a.x = x :=
  (invoked_restrictX.1 (hM.recs.invoked ha)).1

/-- "Only if" part of Theorem 5.1: a linearization of `H`, restricted to `x`, linearizes
`H|x` (assuming the empty history is legal for every object). -/
theorem IsLinA.restrictX {spec : SeqSpec P X Op Res} {H : History P X Op Res}
    {M : List (OpRec P X Op Res)} (hH : WellFormed H) (hM : IsLinA spec H M)
    (hnil : ∀ x, [] ∈ spec x) (x : X) :
    IsLinA spec (restrictX H x) (M.filter (·.x = x)) := by
  have hids : idsOf (M.filter (·.x = x)) = (idsOf M).filter (·.x = x) := by
    simpa using idsOf_filter M (fun _ y => decide (y = x))
  have hzip : (idsOf (M.filter (·.x = x))).zip (M.filter (·.x = x)) =
      ((idsOf M).zip M).filter (fun ae => ae.2.x = x) := by
    simpa using (zip_idsOf_filter M (fun _ y => decide (y = x))).symm
  refine IsLinA.mk' (wellFormed_restrictX hH x) ?_ ?_ ?_ ?_
  · intro a e hae
    rw [hzip, List.mem_filter] at hae
    obtain ⟨hae, hex⟩ := hae
    have hax : a.x = x := by rw [(mem_zip_idsOf hae).2]; simpa using hex
    rw [opOf_restrictX hax, resOf_restrictX hax, completed_restrictX_of_eq hax]
    exact hM.recs a e hae
  · intro a ha
    obtain ⟨hax, ha⟩ := completed_restrictX.1 ha
    rw [hids, List.mem_filter]; exact ⟨hM.complete a ha, by simp [hax]⟩
  · rw [legal_seqHist_iff]
    intro y
    rw [List.filter_filter]
    by_cases hy : x = y
    · subst hy
      have := (legal_seqHist_iff spec M).1 hM.legal x
      convert this using 3; funext e; simp
    · convert hnil y
      have : (M.filter fun e => decide (e.x = y) && decide (e.x = x)) = [] := by
        rw [List.filter_eq_nil_iff]; intro e _; simp only [Bool.and_eq_true, decide_eq_true_eq]
        rintro ⟨rfl, rfl⟩; exact hy rfl
      rw [this]; rfl
  · intro a b hab hb
    rw [hids, List.mem_filter] at hb
    have hbx : b.x = x := by simpa using hb.2
    have hax : a.x = x := (completed_restrictX.1 hab.completed).1
    rw [precedes_restrictX hax hbx] at hab
    rw [hids]
    have := (hM.realtime a b hab hb.1).filter (fun a : OpId P X => decide (a.x = x))
    simpa [hax, hbx] using this

/-! ### Merging per-object linearizations -/

lemma flatMap_ite_eq {α β : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup) (x : α)
    (f : α → List β) :
    l.flatMap (fun y => if y = x then f y else []) = if x ∈ l then f x else [] := by
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons, ih hl.2]
    by_cases hy : y = x
    · subst hy; simp [hl.1]
    · simp [hy, Ne.symm hy]

/-- Two lists with the same sequence of `f`-values and the same sublists of elements with each
given `f`-value are equal. -/
lemma eq_of_map_eq_of_filter_eq {α β : Type*} [DecidableEq β] (f : α → β) :
    ∀ {l₁ l₂ : List α}, l₁.map f = l₂.map f →
      (∀ b, l₁.filter (fun u => f u = b) = l₂.filter (fun u => f u = b)) → l₁ = l₂
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | u :: l₁, v :: l₂, hmap, hfilt => by
    simp only [List.map_cons, List.cons.injEq] at hmap
    have huv : u = v := by
      have := hfilt (f u)
      simp only [List.filter_cons, decide_true, ↓reduceIte, hmap.1] at this
      exact (List.cons.inj this).1
    subst huv
    congr 1
    refine eq_of_map_eq_of_filter_eq f hmap.2 fun b => ?_
    have := hfilt b
    by_cases hb : f u = b
    · simp only [List.filter_cons, hb, decide_true, ↓reduceIte] at this
      exact (List.cons.inj this).2
    · simpa [List.filter_cons, hb] using this

section Merge

variable {spec : SeqSpec P X Op Res} {H : History P X Op Res} (Ms : X → List (OpRec P X Op Res))

/-- Linearization point of `a` (an operation of object `a.x`). -/
def lpOf (a : OpId P X) : ℕ := runMax H (idsOf (Ms a.x)) a

/-- Position of `a` in the linearization of its object. -/
def posOf (a : OpId P X) : ℕ := (idsOf (Ms a.x)).idxOf a

/-- Lexicographic order on (linearization point, position). -/
def keyLE (a b : OpId P X) : Prop :=
  lpOf (H := H) Ms a < lpOf (H := H) Ms b ∨
    (lpOf (H := H) Ms a = lpOf (H := H) Ms b ∧ posOf Ms a ≤ posOf Ms b)

instance (a b : OpId P X) : Decidable (keyLE (H := H) Ms a b) := by
  unfold keyLE; infer_instance

/-- Strict lexicographic order. -/
def keyLT (a b : OpId P X) : Prop :=
  lpOf (H := H) Ms a < lpOf (H := H) Ms b ∨
    (lpOf (H := H) Ms a = lpOf (H := H) Ms b ∧ posOf Ms a < posOf Ms b)

/-- All per-object linearizations, as (identity, record) pairs. -/
def allPairs : List (OpId P X × OpRec P X Op Res) :=
  (H.map Event.obj).dedup.flatMap (fun x => (idsOf (Ms x)).zip (Ms x))

/-- The merged linearization (as identity–record pairs), sorted by key. -/
def merged : List (OpId P X × OpRec P X Op Res) :=
  (allPairs (H := H) Ms).mergeSort (fun u v => decide (keyLE (H := H) Ms u.1 v.1))

variable {Ms}

lemma merged_perm : (merged (H := H) Ms).Perm (allPairs (H := H) Ms) := List.mergeSort_perm _ _

lemma merged_pairwise_le :
    (merged (H := H) Ms).Pairwise (fun u v => keyLE (H := H) Ms u.1 v.1) := by
  have := List.pairwise_mergeSort (le := fun u v : OpId P X × OpRec P X Op Res =>
    decide (keyLE (H := H) Ms u.1 v.1)) ?_ ?_ (allPairs (H := H) Ms)
  · simpa [merged] using this
  · intro u v w h1 h2; simp only [keyLE, decide_eq_true_eq] at *; omega
  · intro u v; simp only [keyLE, Bool.or_eq_true, decide_eq_true_eq]; omega

variable (hMs : ∀ x, IsLinA spec (restrictX H x) (Ms x))
include hMs

lemma mem_ids_obj {x : X} {a : OpId P X} (ha : a ∈ idsOf (Ms x)) : a.x = x :=
  (hMs x).obj_eq ha

lemma mem_ids_invoked {x : X} {a : OpId P X} (ha : a ∈ idsOf (Ms x)) : Invoked H a :=
  (invoked_restrictX.1 ((hMs x).recs.invoked ha)).2

lemma mem_zip_obj {x : X} {a : OpId P X} {e : OpRec P X Op Res}
    (h : (a, e) ∈ (idsOf (Ms x)).zip (Ms x)) : a.x = x ∧ e.x = x := by
  have h1 := mem_ids_obj hMs (mem_idsOf_of_zip h)
  exact ⟨h1, (mem_zip_idsOf h).2 ▸ h1⟩

lemma ids_eq_nil_of_not_mem {x : X} (hx : x ∉ (H.map Event.obj).dedup) : Ms x = [] := by
  rcases hM : Ms x with _ | ⟨e, M⟩
  · rfl
  exfalso
  have ha : (⟨e.p, e.x, 0⟩ : OpId P X) ∈ idsOf (Ms x) := by
    rw [hM, mem_idsOf]; simp [cnt]
  have hax := mem_ids_obj hMs ha
  have hi := mem_ids_invoked hMs ha
  simp only at hax
  apply hx
  rw [List.mem_dedup, List.mem_map]
  obtain ⟨o, h1, -⟩ := tInv_spec hi
  refine ⟨.inv e.p e.x o, List.mem_of_getElem? h1, by simp [hax]⟩

/-- Linearization points of operations of different objects differ; hence keys are
injective. -/
lemma key_inj {x y : X} {a b : OpId P X} (ha : a ∈ idsOf (Ms x)) (hb : b ∈ idsOf (Ms y))
    (hlp : lpOf (H := H) Ms a = lpOf (H := H) Ms b) (hpos : posOf Ms a = posOf Ms b) : a = b := by
  have hax := mem_ids_obj hMs ha
  have hbx := mem_ids_obj hMs hb
  subst hax hbx
  obtain ⟨c, hc, hce⟩ := exists_runMax_eq (H := H) (nodup_idsOf (Ms a.x)) ha
  obtain ⟨d, hd, hde⟩ := exists_runMax_eq (H := H) (nodup_idsOf (Ms b.x)) hb
  have hcm : c ∈ idsOf (Ms a.x) := by
    rcases hc with h | rfl
    exacts [h.subset (by simp), ha]
  have hdm : d ∈ idsOf (Ms b.x) := by
    rcases hd with h | rfl
    exacts [h.subset (by simp), hb]
  have hcd : c = d := tInv_inj (mem_ids_invoked hMs hcm) (mem_ids_invoked hMs hdm)
    (by unfold lpOf at hlp; rw [← hce, ← hde]; exact hlp)
  have hxy : a.x = b.x := by
    rw [← mem_ids_obj hMs hcm, ← mem_ids_obj hMs hdm, hcd]
  unfold posOf at hpos
  rw [hxy] at ha hpos
  exact (List.idxOf_inj ha).1 hpos

lemma zip_pairwise (x : X) :
    ((idsOf (Ms x)).zip (Ms x)).Pairwise (fun u v => keyLT (H := H) Ms u.1 v.1) := by
  have : (idsOf (Ms x)).Pairwise (keyLT (H := H) Ms) := by
    rw [List.pairwise_iff_forall_sublist]
    intro a b hab
    have ha : a ∈ idsOf (Ms x) := hab.subset (by simp)
    have hb : b ∈ idsOf (Ms x) := hab.subset (by simp)
    have hax := mem_ids_obj hMs ha
    have hbx := mem_ids_obj hMs hb
    have h1 := runMax_mono (H := H) (nodup_idsOf _) hab
    have h2 := ((pair_sublist_iff_idxOf (nodup_idsOf _)).1 hab).2.2
    unfold keyLT lpOf posOf; rw [hax, hbx]; omega
  have h := List.pairwise_map.1 (by rwa [List.map_fst_zip (by simp)] :
    ((idsOf (Ms x)).zip (Ms x) |>.map Prod.fst).Pairwise (keyLT (H := H) Ms))
  exact h

lemma allPairs_filter (x : X) :
    (allPairs (H := H) Ms).filter (fun u => u.2.x = x) = (idsOf (Ms x)).zip (Ms x) := by
  unfold allPairs
  rw [List.filter_flatMap]
  have hz : ∀ y, ((idsOf (Ms y)).zip (Ms y)).filter (fun u => u.2.x = x) =
      if y = x then (idsOf (Ms y)).zip (Ms y) else [] := by
    intro y
    split_ifs with hy
    · rw [List.filter_eq_self]; intro u hu; simp [(mem_zip_obj hMs hu).2, hy]
    · rw [List.filter_eq_nil_iff]; intro u hu; simp [(mem_zip_obj hMs hu).2, hy]
  simp only [hz]
  rw [flatMap_ite_eq (List.nodup_dedup _) x (fun y => (idsOf (Ms y)).zip (Ms y))]
  split_ifs with hx
  · rfl
  · rw [ids_eq_nil_of_not_mem hMs hx]; rfl

lemma mem_allPairs {u : OpId P X × OpRec P X Op Res} (hu : u ∈ allPairs (H := H) Ms) :
    u ∈ (idsOf (Ms u.2.x)).zip (Ms u.2.x) := by
  unfold allPairs at hu
  obtain ⟨y, -, hy⟩ := List.mem_flatMap.1 hu
  rw [(mem_zip_obj hMs hy).2]; exact hy

lemma allPairs_nodup : ((allPairs (H := H) Ms).map Prod.fst).Nodup := by
  unfold allPairs
  rw [List.map_flatMap]
  have hz : ∀ x, ((idsOf (Ms x)).zip (Ms x)).map Prod.fst = idsOf (Ms x) :=
    fun x => List.map_fst_zip (by simp)
  simp only [hz]
  rw [List.nodup_flatMap]
  refine ⟨fun x _ => nodup_idsOf _, ?_⟩
  refine (List.nodup_dedup _).imp fun {x y} hxy => ?_
  change List.Disjoint _ _
  rw [List.disjoint_left]
  intro a ha hb
  exact hxy ((mem_ids_obj hMs ha).symm.trans (mem_ids_obj hMs hb))

lemma merged_pairwise_lt :
    (merged (H := H) Ms).Pairwise (fun u v => keyLT (H := H) Ms u.1 v.1) := by
  have hnd : ((merged (H := H) Ms).map Prod.fst).Nodup :=
    ((merged_perm (H := H)).map Prod.fst).nodup_iff.2 (allPairs_nodup hMs)
  rw [List.Nodup, List.pairwise_map] at hnd
  refine ((merged_pairwise_le (H := H)).and hnd).imp_of_mem ?_
  intro u v hu hv ⟨hle, hne⟩
  have hu' := mem_idsOf_of_zip (mem_allPairs hMs ((merged_perm (H := H)).subset hu))
  have hv' := mem_idsOf_of_zip (mem_allPairs hMs ((merged_perm (H := H)).subset hv))
  unfold keyLE at hle; unfold keyLT
  rcases hle with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, lt_of_le_of_ne h2 fun h3 => hne (key_inj hMs hu' hv' h1 h3)⟩

lemma merged_filter (x : X) :
    (merged (H := H) Ms).filter (fun u => u.2.x = x) = (idsOf (Ms x)).zip (Ms x) := by
  refine List.Perm.eq_of_pairwise (le := fun u v => keyLT (H := H) Ms u.1 v.1) ?_ ?_
    (zip_pairwise hMs x) ?_
  · intro u v _ _ h1 h2; unfold keyLT at h1 h2; omega
  · exact (merged_pairwise_lt hMs).sublist List.filter_sublist
  · rw [← allPairs_filter hMs x]; exact (merged_perm (H := H)).filter _

/-- The merged linearization. -/
def mergedM (Ms : X → List (OpRec P X Op Res)) : List (OpRec P X Op Res) :=
  (merged (H := H) Ms).map Prod.snd

lemma mergedM_filter (x : X) : (mergedM (H := H) Ms).filter (·.x = x) = Ms x := by
  unfold mergedM
  have := congrArg (List.map Prod.snd) (merged_filter hMs x)
  rw [List.map_snd_zip (by simp)] at this
  rw [← this, List.filter_map]; rfl

lemma zip_mergedM :
    (idsOf (mergedM (H := H) Ms)).zip (mergedM (H := H) Ms) = merged (H := H) Ms := by
  apply eq_of_map_eq_of_filter_eq (fun u : OpId P X × OpRec P X Op Res => u.2.x)
  · rw [show (fun u : OpId P X × OpRec P X Op Res => u.2.x) = OpRec.x ∘ Prod.snd from rfl,
      ← List.map_map, ← List.map_map, List.map_snd_zip (by simp)]
    rfl
  · intro x
    have h1 := (zip_idsOf_filter (mergedM (H := H) Ms) (fun _ y => decide (y = x)))
    rw [h1, mergedM_filter hMs x, merged_filter hMs x]

lemma idsOf_mergedM : idsOf (mergedM (H := H) Ms) = (merged (H := H) Ms).map Prod.fst := by
  rw [← zip_mergedM hMs, List.map_fst_zip (by simp)]

/-- The merged list linearizes `H`. -/
theorem isLinA_mergedM (hH : WellFormed H) : IsLinA spec H (mergedM (H := H) Ms) := by
  have hmem : ∀ a, a ∈ idsOf (mergedM (H := H) Ms) → a ∈ idsOf (Ms a.x) := by
    intro a ha
    rw [idsOf_mergedM hMs, List.mem_map] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    have := mem_allPairs hMs ((merged_perm (H := H)).subset hu)
    have hx := (mem_zip_obj hMs this).1
    rw [← (mem_zip_obj hMs this).2] at hx
    rw [hx]; exact mem_idsOf_of_zip this
  refine IsLinA.mk' hH ?_ ?_ ?_ ?_
  · intro a e hae
    rw [zip_mergedM hMs] at hae
    have h := mem_allPairs hMs ((merged_perm (H := H)).subset hae)
    have hx := (mem_zip_obj hMs h)
    have hrec := (hMs e.x).recs a e h
    rw [opOf_restrictX hx.1, resOf_restrictX hx.1, completed_restrictX_of_eq hx.1] at hrec
    exact hrec
  · intro a ha
    have hc : Completed (restrictX H a.x) a := completed_restrictX.2 ⟨rfl, ha⟩
    have ha' := (hMs a.x).complete a hc
    obtain ⟨e, he⟩ := exists_mem_zip_idsOf ha'
    have hex := (mem_zip_obj hMs he)
    have hobj : a.x ∈ (H.map Event.obj).dedup := by
      by_contra hn
      rw [ids_eq_nil_of_not_mem hMs hn] at ha'; simp at ha'
    have : (a, e) ∈ allPairs (H := H) Ms := List.mem_flatMap.2 ⟨a.x, hobj, he⟩
    rw [idsOf_mergedM hMs]
    exact List.mem_map.2 ⟨(a, e), (merged_perm (H := H)).symm.subset this, rfl⟩
  · rw [legal_seqHist_iff]
    intro y
    rw [mergedM_filter hMs y]
    have := (legal_seqHist_iff spec (Ms y)).1 (hMs y).legal y
    convert this using 2
    symm; rw [List.filter_eq_self]
    intro e he
    obtain ⟨a, ha⟩ : ∃ a, (a, e) ∈ (idsOf (Ms y)).zip (Ms y) := by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
      exact ⟨(idsOf (Ms y))[i]'(by simpa using hi), List.mem_iff_getElem.2 ⟨i, by simpa using hi,
        by simp⟩⟩
    simp [(mem_zip_obj hMs ha).2]
  · intro a b hab hb
    have hac := hab.completed
    have ha : a ∈ idsOf (mergedM (H := H) Ms) := by
      -- completed operations are linearized (second field)
      have hc : Completed (restrictX H a.x) a := completed_restrictX.2 ⟨rfl, hac⟩
      have ha' := (hMs a.x).complete a hc
      obtain ⟨e, he⟩ := exists_mem_zip_idsOf ha'
      have hobj : a.x ∈ (H.map Event.obj).dedup := by
        by_contra hn
        rw [ids_eq_nil_of_not_mem hMs hn] at ha'; simp at ha'
      have : (a, e) ∈ allPairs (H := H) Ms := List.mem_flatMap.2 ⟨a.x, hobj, he⟩
      rw [idsOf_mergedM hMs]
      exact List.mem_map.2 ⟨(a, e), (merged_perm (H := H)).symm.subset this, rfl⟩
    have haM := hmem a ha
    have hbM := hmem b hb
    -- the linearization point of `a` is before its response
    have h1 : lpOf (H := H) Ms a < tRes H a := by
      unfold lpOf
      refine runMax_lt_tRes hH (nodup_idsOf _) (fun c hc => mem_ids_invoked hMs hc) ?_ haM hac
      intro c hc hac'
      have hcx := mem_ids_obj hMs hc
      exact (hMs a.x).realtime a c ((precedes_restrictX rfl hcx).2 hac') hc
    have h2 : tInv H b ≤ lpOf (H := H) Ms b := le_runMax (nodup_idsOf _) hbM (Or.inr rfl)
    have h3 := (precedes_iff.1 hab).2
    have hlt : keyLT (H := H) Ms a b := Or.inl (by omega)
    have hne : a ≠ b := by rintro rfl; omega
    have hpw : (idsOf (mergedM (H := H) Ms)).Pairwise (keyLT (H := H) Ms) := by
      rw [idsOf_mergedM hMs, List.pairwise_map]; exact merged_pairwise_lt hMs
    rcases pair_sublist_total (nodup_idsOf _) ha hb hne with h | h
    · exact h
    · have := List.pairwise_iff_forall_sublist.1 hpw h
      unfold keyLT at this hlt; omega

end Merge

/-- "If" part of Theorem 5.1, list form. -/
theorem exists_isLinA_of_restrictX {spec : SeqSpec P X Op Res} {H : History P X Op Res}
    (hH : WellFormed H) (h : ∀ x, ∃ M, IsLinA spec (restrictX H x) M) :
    ∃ M, IsLinA spec H M := by
  choose Ms hMs using h
  exact ⟨_, isLinA_mergedM hMs hH⟩

/-- **Theorem 5.1** (locality; Herlihy–Wing Theorem 1) for the amended definition: a
(well-formed) history `H` is linearizable iff `H|x` is linearizable for every object `x`.
We assume that the empty history is legal for every object (sequential specifications are
nonempty and prefix-closed); this is only used in the "only if" direction. -/
theorem locality {spec : SeqSpec P X Op Res} {H : History P X Op Res} (hH : WellFormed H)
    (hnil : ∀ x, [] ∈ spec x) :
    Linearizable spec H ↔ ∀ x, Linearizable spec (restrictX H x) := by
  constructor
  · intro h x
    obtain ⟨-, M, hM⟩ := linearizable_iff.1 h
    exact linearizable_iff.2 ⟨wellFormed_restrictX hH x, _, hM.restrictX hH hnil x⟩
  · intro h
    obtain ⟨M, hM⟩ := exists_isLinA_of_restrictX hH fun x => (linearizable_iff.1 (h x)).2
    exact linearizable_iff.2 ⟨hH, M, hM⟩

/-- The "if" direction of Theorem 5.1 needs no assumption on the specification. -/
theorem linearizable_of_restrictX {spec : SeqSpec P X Op Res} {H : History P X Op Res}
    (hH : WellFormed H) (h : ∀ x, Linearizable spec (restrictX H x)) : Linearizable spec H := by
  obtain ⟨M, hM⟩ := exists_isLinA_of_restrictX hH fun x => (linearizable_iff.1 (h x)).2
  exact linearizable_iff.2 ⟨hH, M, hM⟩

end Cslib.SharedMemory.HerlihyWing
