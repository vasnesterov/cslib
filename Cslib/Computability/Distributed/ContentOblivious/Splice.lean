/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.ContentOblivious.Model

/-!
# Executions as lists of deliveries, interface traces, and splicing

An execution fragment is a list of delivered ports `(v, j)` (node `v` consumes a pulse from its port
`j`); `ValidSteps W A c l` says that every delivery is enabled when it happens,
`runSteps A c l` is the
resulting configuration. `reach_iff_validSteps` relates this to `Reach`.

A *labelling* `lab : V × Bool → Option Λ` names some ports (the receiving ports of a cut, e.g. the
boundary of an interval of a ring); the *interface trace* of an execution `l` is the word
`l.filterMap lab` of labels of the boundary deliveries, in execution order.

**Splicing** (`splice`): the crossing-sequence argument for content-oblivious networks. Take two
executions `l true`, `l false` of the same algorithm on the same wiring `W`, with two labellings
`lab true`, `lab false`, whose interface traces are equal. Build a new network `W'` whose nodes `v`
are copies (`f v`) of nodes of `W` coming from the *inside* of the cut of `lab true`
(`side v = true`) or from the *outside* of the cut of `lab false` (`side v = false`), wired as in
`W` except across the cut, where the boundary port named `μ` of one side is linked to the peer of
the port named `μ` of the other side (`SpliceData`). Then `W'` has an execution in which every node
ends in the same local state, with the same pulse counters, as its original in the corresponding
execution. Pulses carry no content, so only the order of the boundary deliveries matters.
-/

@[expose] public section

namespace Cslib.ContentOblivious

open Finset

section lists

variable {V : Type*} [DecidableEq V] (W : Wiring V) (A : Algo)

/-- The configuration after delivering the pulses of the list `l` in order (no enabledness
check). -/
def runSteps (c : Config V A.State) (l : List (V × Bool)) : Config V A.State :=
  l.foldl (fun c p => deliver A c p.1 p.2) c

/-- The list `l` of deliveries is a valid execution fragment from `c`: each delivery is enabled. -/
def ValidSteps : Config V A.State → List (V × Bool) → Prop
  | _, [] => True
  | c, p :: l => Enabled W A c p.1 p.2 ∧ ValidSteps (deliver A c p.1 p.2) l

variable {W A}

/-- Delivering no pulse. -/
@[simp] lemma runSteps_nil (c : Config V A.State) : runSteps A c [] = c := rfl

/-- Delivering a list of pulses, first step. -/
@[simp] lemma runSteps_cons (c : Config V A.State) (p : V × Bool) (l : List (V × Bool)) :
    runSteps A c (p :: l) = runSteps A (deliver A c p.1 p.2) l := rfl

/-- Delivering a concatenation of lists of pulses. -/
lemma runSteps_append (c : Config V A.State) (l₁ l₂ : List (V × Bool)) :
    runSteps A c (l₁ ++ l₂) = runSteps A (runSteps A c l₁) l₂ := by
  simp [runSteps, List.foldl_append]

/-- The empty fragment is valid. -/
@[simp] lemma validSteps_nil (c : Config V A.State) : ValidSteps W A c [] := trivial

/-- A fragment is valid iff its first delivery is enabled and the rest is valid. -/
@[simp] lemma validSteps_cons (c : Config V A.State) (p : V × Bool) (l : List (V × Bool)) :
    ValidSteps W A c (p :: l) ↔
      Enabled W A c p.1 p.2 ∧ ValidSteps W A (deliver A c p.1 p.2) l := Iff.rfl

/-- Validity of a concatenation of fragments. -/
lemma validSteps_append (c : Config V A.State) (l₁ l₂ : List (V × Bool)) :
    ValidSteps W A c (l₁ ++ l₂) ↔ ValidSteps W A c l₁ ∧ ValidSteps W A (runSteps A c l₁) l₂ := by
  induction l₁ generalizing c with
  | nil => simp
  | cons p l ih => simp [ih, and_assoc]

/-- A valid fragment is an execution. -/
lemma ValidSteps.reflTransGen {c : Config V A.State} {l : List (V × Bool)}
    (h : ValidSteps W A c l) :
    Relation.ReflTransGen (Step W A) c (runSteps A c l) := by
  induction l generalizing c with
  | nil => exact .refl
  | cons p l ih => exact .head (Step.mk c p.1 p.2 h.1) (ih h.2)

/-- Every execution is a valid fragment. -/
lemma exists_validSteps_of_reflTransGen {c c' : Config V A.State}
    (h : Relation.ReflTransGen (Step W A) c c') :
    ∃ l, ValidSteps W A c l ∧ runSteps A c l = c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], trivial, rfl⟩
  | head hs _ ih =>
    obtain ⟨l, hl, rfl⟩ := ih
    obtain ⟨v, j, hen⟩ := hs
    exact ⟨(v, j) :: l, ⟨hen, hl⟩, rfl⟩

/-- Reachable configurations are exactly the results of valid lists of deliveries. -/
lemma reach_iff_validSteps (id : V → ℕ) (c : Config V A.State) :
    Reach W A id c ↔ ∃ l, ValidSteps W A (initCfg A id) l ∧ runSteps A (initCfg A id) l = c :=
  ⟨exists_validSteps_of_reflTransGen, fun ⟨_, hl, h⟩ => h ▸ hl.reflTransGen⟩

/-- The number of pulses received at a port is the number of its deliveries. -/
lemma runSteps_recvd (c : Config V A.State) (l : List (V × Bool)) (p : V × Bool) :
    (runSteps A c l).recvd p = c.recvd p + l.count p := by
  induction l generalizing c with
  | nil => simp
  | cons q l ih =>
    rw [runSteps_cons, ih, deliver_recvd, List.count_cons]
    by_cases h : q = p
    · subst h; simp; omega
    · simp [h, Ne.symm h]

/-- From the initial configuration, the received counters count the deliveries. -/
lemma runSteps_initCfg_recvd (id : V → ℕ) (l : List (V × Bool)) (p : V × Bool) :
    (runSteps A (initCfg A id) l).recvd p = l.count p := by
  simp [runSteps_recvd, initCfg]

end lists

/-! ### Splicing -/

/-- Node `v` of `c'` has the same local state and pulse counters as node `u` of `d`. -/
def NodeAgree {V V' S : Type*} (d : Config V S) (u : V) (c' : Config V' S) (v : V') : Prop :=
  c'.st v = d.st u ∧ ∀ j, c'.sent (v, j) = d.sent (u, j) ∧ c'.recvd (v, j) = d.recvd (u, j)

/-- The data of a splice of two cuts of a wiring `W` into a new wiring `W'` (see the module
docstring). `lab b` names the boundary ports (receiving ends of the links crossing the cut) of the
cut used on side `b`; `own μ` is the side on which the port named `μ` lies in the new network. -/
structure SpliceData {V V' : Type*} (W : Wiring V) (W' : Wiring V') (Λ : Type*) where
  /-- The side a node of the new network comes from. -/
  side : V' → Bool
  /-- The original of a node of the new network. -/
  f : V' → V
  /-- The labellings of boundary ports of the two cuts. -/
  lab : Bool → V × Bool → Option Λ
  /-- The side owning the receiving port of a label. -/
  own : Λ → Bool
  /-- Nodes of the same side have distinct originals. -/
  f_inj : ∀ v w, side v = side w → f v = f w → v = w
  /-- Each label names at most one port of a cut. -/
  lab_inj : ∀ b p q μ, lab b p = some μ → lab b q = some μ → p = q
  /-- A port is unlabelled iff its link stays inside its side. -/
  internal : ∀ v j, lab (side v) (f v, j) = none ↔ side (W'.peer (v, j)).1 = side v
  /-- Links inside a side are links of `W`. -/
  peer_int : ∀ v j, side (W'.peer (v, j)).1 = side v →
    W.peer (f v, j) = (f (W'.peer (v, j)).1, (W'.peer (v, j)).2)
  /-- A label is owned by side `b` iff its port lies in side `b`. -/
  own_iff : ∀ b p μ, lab b p = some μ → (own μ = b ↔ ∃ v, side v = b ∧ f v = p.1)
  /-- Links across the cut: the port named `μ` on its own side is linked in `W'` to the copy of the
  peer (in `W`) of the port named `μ` of the other cut. -/
  cross : ∀ v j μ q, lab (side v) (f v, j) = some μ → own μ = side v → lab (!side v) q = some μ →
    W.peer q = (f (W'.peer (v, j)).1, (W'.peer (v, j)).2)

namespace SpliceData

variable {V V' Λ : Type*} [DecidableEq V] [DecidableEq V'] {W : Wiring V} {W' : Wiring V'}
  {A : Algo} (D : SpliceData W W' Λ)

/-- Every node of the new network agrees with its original in the configuration of its side. -/
def AgreeAll (c : Bool → Config V A.State) (c' : Config V' A.State) : Prop :=
  ∀ v, NodeAgree (c (D.side v)) (D.f v) c' v

/-- Boundary ports with the same name have received the same number of pulses on both sides. -/
def Counts (c : Bool → Config V A.State) : Prop :=
  ∀ b μ p q, D.lab b p = some μ → D.lab (!b) q = some μ → (c b).recvd p = (c (!b)).recvd q

/-- A Boolean is either `b` or `!b`. -/
lemma bool_cases (b b' : Bool) : b' = b ∨ b' = !b := by cases b <;> cases b' <;> simp

/-- Deliver at a node of side `b` and at its copy. -/
lemma agreeAll_deliver {c c₁ : Bool → Config V A.State} {c' : Config V' A.State}
    (h : D.AgreeAll c c') {b : Bool} {v : V'} (hv : D.side v = b) (j : Bool)
    (h₁ : c₁ b = deliver A (c b) (D.f v) j) (h₂ : c₁ (!b) = c (!b)) :
    D.AgreeAll c₁ (deliver A c' v j) := by
  subst hv
  intro w
  obtain ⟨hst, hcnt⟩ := h w
  have hv' := h v
  rcases bool_cases (D.side v) (D.side w) with hw | hw
  · rw [hw, h₁]
    have key : D.f w = D.f v ↔ w = v := ⟨D.f_inj w v hw, fun h => h ▸ rfl⟩
    rw [hw] at hst hcnt
    refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
    · by_cases hwv : w = v
      · subst hwv; simp [deliver_st_self, hst]
      · rw [deliver_st_ne _ _ _ _ hwv, deliver_st_ne _ _ _ _ (mt key.1 hwv), hst]
    · rw [deliver_sent, deliver_sent, (hcnt i).1]
      by_cases hwv : w = v
      · subst hwv; simp [hv'.1]
      · simp [hwv, mt key.1 hwv]
    · rw [deliver_recvd, deliver_recvd, (hcnt i).2]
      by_cases hwv : w = v
      · subst hwv; simp
      · simp [hwv, mt key.1 hwv]
  · rw [hw, h₂]
    have hwv : w ≠ v := by rintro rfl; cases hh : D.side w <;> simp [hh] at hw
    rw [hw] at hst hcnt
    refine ⟨by rw [deliver_st_ne _ _ _ _ hwv, hst], fun i => ⟨?_, ?_⟩⟩
    · rw [deliver_sent, (hcnt i).1]; simp [hwv]
    · rw [deliver_recvd, (hcnt i).2]; simp [hwv]

omit [DecidableEq V'] in
/-- Deliver at a node of side `b`'s execution that has no copy. -/
lemma agreeAll_skip {c c₁ : Bool → Config V A.State} {c' : Config V' A.State}
    (h : D.AgreeAll c c') {b : Bool} {u : V} (hu : ¬ ∃ v, D.side v = b ∧ D.f v = u) (j : Bool)
    (h₁ : c₁ b = deliver A (c b) u j) (h₂ : c₁ (!b) = c (!b)) :
    D.AgreeAll c₁ c' := by
  intro w
  obtain ⟨hst, hcnt⟩ := h w
  rcases bool_cases b (D.side w) with hw | hw
  · rw [hw, h₁]
    rw [hw] at hst hcnt
    have hne : D.f w ≠ u := fun he => hu ⟨w, hw, he⟩
    refine ⟨by rw [deliver_st_ne _ _ _ _ hne, hst], fun i => ⟨?_, ?_⟩⟩
    · rw [deliver_sent, (hcnt i).1]; simp [hne]
    · rw [deliver_recvd, (hcnt i).2]; simp [hne]
  · rw [hw, h₂]; rw [hw] at hst hcnt; exact ⟨hst, hcnt⟩

omit [DecidableEq V] [DecidableEq V'] in
/-- A delivery enabled in an original execution is enabled at its copy, provided a pulse is in
transit there. -/
lemma enabled_copy {c : Bool → Config V A.State} {c' : Config V' A.State}
    (h : D.AgreeAll c c') {v : V'} {j : Bool} (hen : Enabled W A (c (D.side v)) (D.f v) j)
    (hlt : c'.recvd (v, j) < c'.sent (W'.peer (v, j))) : Enabled W' A c' v j := by
  obtain ⟨hst, -⟩ := h v
  exact ⟨hst ▸ hen.1, hst ▸ hen.2.1, hlt⟩

/-- One step of the side-`b` execution at an unlabelled port. -/
lemma step_internal {c : Bool → Config V A.State} {c' : Config V' A.State}
    (h : D.AgreeAll c c') (hc : D.Counts c) {b : Bool} {p : V × Bool} (hp : D.lab b p = none)
    (hen : Enabled W A (c b) p.1 p.2) :
    ∃ l₀, ValidSteps W' A c' l₀ ∧
      D.AgreeAll (Function.update c b (deliver A (c b) p.1 p.2)) (runSteps A c' l₀) ∧
      D.Counts (Function.update c b (deliver A (c b) p.1 p.2)) := by
  have hcnt : D.Counts (Function.update c b (deliver A (c b) p.1 p.2)) := by
    have key : ∀ b' q μ, D.lab b' q = some μ →
        (Function.update c b (deliver A (c b) p.1 p.2) b').recvd q = (c b').recvd q := by
      intro b' q μ hq
      rcases bool_cases b b' with rfl | rfl
      · have : q ≠ p := by rintro rfl; rw [hp] at hq; cases hq
        simp [deliver_recvd, this]
      · simp
    intro b' μ q q' hq hq'
    rw [key _ _ _ hq, key _ _ _ hq']; exact hc b' μ q q' hq hq'
  by_cases hex : ∃ v, D.side v = b ∧ D.f v = p.1
  · obtain ⟨v, hv, hfv⟩ := hex
    refine ⟨[(v, p.2)], ⟨?_, trivial⟩, ?_, hcnt⟩
    · refine D.enabled_copy h (by rw [hv, hfv]; exact hen) ?_
      obtain ⟨u, j⟩ := p
      dsimp only at hfv hen ⊢
      subst hfv
      have hint := (D.internal v j).1 (by rw [hv]; exact hp)
      have hpeer := D.peer_int v j hint
      obtain ⟨-, h1⟩ := h v
      obtain ⟨-, h2⟩ := h (W'.peer (v, j)).1
      rw [(h1 j).2, (h2 _).1, hint, hv, ← hpeer]
      exact hen.2.2
    · simp only [runSteps_cons, runSteps_nil]
      exact D.agreeAll_deliver h hv p.2 (by simp [hfv]) (by simp)
  · exact ⟨[], trivial, D.agreeAll_skip h hex p.2 (by simp) (by simp), hcnt⟩

/-- One synchronised boundary step: both executions deliver a pulse at a port named `μ`. -/
lemma step_sync {c : Bool → Config V A.State} {c' : Config V' A.State}
    (h : D.AgreeAll c c') (hc : D.Counts c) {pp : Bool → V × Bool} {μ : Λ}
    (hp : ∀ b, D.lab b (pp b) = some μ) (hen : ∀ b, Enabled W A (c b) (pp b).1 (pp b).2) :
    ∃ l₀, ValidSteps W' A c' l₀ ∧
      D.AgreeAll (fun b => deliver A (c b) (pp b).1 (pp b).2) (runSteps A c' l₀) ∧
      D.Counts (fun b => deliver A (c b) (pp b).1 (pp b).2) := by
  set b := D.own μ with hb
  obtain ⟨v, hv, hfv⟩ := (D.own_iff b (pp b) μ (hp b)).1 rfl
  have hnex : ¬ ∃ w, D.side w = !b ∧ D.f w = (pp (!b)).1 := by
    rw [← D.own_iff (!b) (pp (!b)) μ (hp _), ← hb]; cases b <;> simp
  have hcnt : D.Counts (fun b => deliver A (c b) (pp b).1 (pp b).2) := by
    classical
    have key : ∀ b' q μ', D.lab b' q = some μ' →
        (deliver A (c b') (pp b').1 (pp b').2).recvd q =
          (c b').recvd q + if μ' = μ then 1 else 0 := by
      intro b' q μ' hq
      rw [deliver_recvd]
      by_cases hμ : μ' = μ
      · subst hμ; have := D.lab_inj _ _ _ _ hq (hp b'); simp [this]
      · have : q ≠ pp b' := by rintro rfl; rw [hp] at hq; exact hμ (Option.some_inj.1 hq).symm
        simp [this, hμ]
    intro b' μ' q q' hq hq'
    simp only
    rw [key _ _ _ hq, key _ _ _ hq', hc b' μ' q q' hq hq']
  have hpb : pp b = (D.f v, (pp b).2) := by rw [hfv]
  have hlab : D.lab (D.side v) (D.f v, (pp b).2) = some μ := by rw [hv, ← hpb]; exact hp b
  refine ⟨[(v, (pp b).2)], ⟨?_, trivial⟩, ?_, hcnt⟩
  · refine D.enabled_copy h (by rw [hv, hfv]; exact hen b) ?_
    have hside : D.side (W'.peer (v, (pp b).2)).1 = !b := by
      have hne := mt (D.internal v (pp b).2).2 (by rw [hlab]; simp)
      rw [hv] at hne
      exact (bool_cases b _).resolve_left hne
    have hcross := D.cross v (pp b).2 μ (pp (!b)) hlab (by rw [hv]) (by rw [hv]; exact hp _)
    obtain ⟨-, h1⟩ := h v
    obtain ⟨-, h2⟩ := h (W'.peer (v, (pp b).2)).1
    rw [(h1 _).2, (h2 _).1, hside, hv, ← hpb, ← hcross, hc b μ _ _ (hp b) (hp _)]
    exact (hen _).2.2
  · simp only [runSteps_cons, runSteps_nil]
    have h₁ := D.agreeAll_deliver (c₁ := Function.update c b (deliver A (c b) (pp b).1 (pp b).2))
      h hv (pp b).2 (by simp [hfv]) (by cases b <;> simp)
    refine D.agreeAll_skip h₁ hnex (pp (!b)).2 (b := !b) ?_ (by simp)
    cases b <;> simp

/-- The splicing construction, by induction on the total length of the two executions. -/
lemma splice_aux (N : ℕ) : ∀ (l : Bool → List (V × Bool)) (c : Bool → Config V A.State)
    (c' : Config V' A.State), (l true).length + (l false).length ≤ N →
    (∀ b, ValidSteps W A (c b) (l b)) →
    (l true).filterMap (D.lab true) = (l false).filterMap (D.lab false) →
    D.AgreeAll c c' → D.Counts c →
    ∃ l', ValidSteps W' A c' l' ∧
      D.AgreeAll (fun b => runSteps A (c b) (l b)) (runSteps A c' l') := by
  induction N with
  | zero =>
    intro l c c' hN _ _ h _
    have h1 : l true = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : l false = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨[], trivial, ?_⟩
    intro v; have := h v; cases hs : D.side v <;> simp_all
  | succ N ih =>
    intro l c c' hN hl htr h hc
    by_cases hint : ∃ b p rest, l b = p :: rest ∧ D.lab b p = none
    · obtain ⟨b, p, rest, hlb, hp⟩ := hint
      have hv := hl b; rw [hlb] at hv
      obtain ⟨l₀, hl₀, h₀, hc₀⟩ := D.step_internal h hc hp hv.1
      have hlen : ((Function.update l b rest) true).length +
          ((Function.update l b rest) false).length ≤ N := by
        cases b <;> simp <;> simp [hlb] at hN <;> omega
      obtain ⟨l₁, hl₁, h₁⟩ := ih (Function.update l b rest) _ _ hlen
        (by intro b'; rcases bool_cases b b' with rfl | rfl
            · simpa using hv.2
            · simpa using hl _)
        (by cases b <;> simpa [hlb, hp] using htr)
        h₀ hc₀
      refine ⟨l₀ ++ l₁, (validSteps_append _ _ _).2 ⟨hl₀, hl₁⟩, ?_⟩
      rw [runSteps_append]
      convert h₁ using 2 with b'
      rcases bool_cases b b' with rfl | rfl
      · simp [hlb]
      · simp
    · push Not at hint
      rcases ht : l true with _ | ⟨p, lt⟩ <;> rcases hf : l false with _ | ⟨q, lf⟩
      · refine ⟨[], trivial, ?_⟩
        intro v; have := h v; cases hs : D.side v <;> simp_all
      · exfalso
        obtain ⟨μ, hμ⟩ := Option.ne_none_iff_exists'.1 (hint false q lf hf)
        rw [ht, hf, List.filterMap_cons_some hμ] at htr; simp at htr
      · exfalso
        obtain ⟨μ, hμ⟩ := Option.ne_none_iff_exists'.1 (hint true p lt ht)
        rw [ht, hf, List.filterMap_cons_some hμ] at htr; simp at htr
      · obtain ⟨μ, hμ⟩ := Option.ne_none_iff_exists'.1 (hint true p lt ht)
        obtain ⟨μ', hμ'⟩ := Option.ne_none_iff_exists'.1 (hint false q lf hf)
        rw [ht, hf, List.filterMap_cons_some hμ, List.filterMap_cons_some hμ'] at htr
        obtain ⟨rfl, htr⟩ := List.cons_eq_cons.1 htr
        let pp : Bool → V × Bool := fun b => cond b p q
        have hv1 := hl true; rw [ht] at hv1
        have hv2 := hl false; rw [hf] at hv2
        obtain ⟨l₀, hl₀, h₀, hc₀⟩ := D.step_sync (pp := pp) (μ := μ) h hc
          (by intro b; cases b <;> simpa [pp]) (by intro b; cases b <;> simp [pp, hv1.1, hv2.1])
        obtain ⟨l₁, hl₁, h₁⟩ := ih (fun b => cond b lt lf) _ _
          (by simp [ht, hf] at hN; simp; omega)
          (by intro b; cases b <;> simp [pp, hv1.2, hv2.2]) (by simpa using htr) h₀ hc₀
        refine ⟨l₀ ++ l₁, (validSteps_append _ _ _).2 ⟨hl₀, hl₁⟩, ?_⟩
        rw [runSteps_append]
        convert h₁ using 2 with b'
        cases b' <;> simp [ht, hf, pp]

end SpliceData

/-- **Splicing.** If two executions have the same interface trace (for the two labellings of a
`SpliceData`), the spliced network `W'` has an execution in which every node ends in the same local
state, with the same pulse counters, as its original in the execution of its side. -/
theorem splice {V V' Λ : Type*} [DecidableEq V] [DecidableEq V'] {W : Wiring V} {W' : Wiring V'}
    {A : Algo} (D : SpliceData W W' Λ) (id : Bool → V → ℕ) (id' : V' → ℕ)
    (hid : ∀ v, id' v = id (D.side v) (D.f v))
    (l : Bool → List (V × Bool)) (hl : ∀ b, ValidSteps W A (initCfg A (id b)) (l b))
    (htr : (l true).filterMap (D.lab true) = (l false).filterMap (D.lab false)) :
    ∃ c', Reach W' A id' c' ∧
      ∀ v, NodeAgree (runSteps A (initCfg A (id (D.side v))) (l (D.side v))) (D.f v) c' v := by
  obtain ⟨l', hl', h⟩ := D.splice_aux _ l (fun b => initCfg A (id b)) (initCfg A id') le_rfl hl htr
    (by intro v; simp [NodeAgree, initCfg, hid])
    (by intro b μ p q _ _; simp [initCfg])
  exact ⟨_, hl'.reflTransGen, h⟩

end Cslib.ContentOblivious
