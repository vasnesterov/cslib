/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.ColourSystem.Algorithm

/-!
# Synchronous message passing in anonymous edge-coloured networks

The operational model of [HirvonenSuomela2012] (§1.2): each node of a `k`-edge-coloured
graph initially knows the colours of its incident edges; in every round each node sends a message
along each incident edge (the edge colour serves as port number), receives the messages of its
neighbours, and updates its state; after `r` rounds it outputs its part of the solution.
There are no identifiers, the algorithm is deterministic, messages and local computation are
unbounded.

We relate this model to the view-based definition used in the proofs of [HirvonenSuomela2012]
(`Cslib.ColourSystem.Algorithm`):

* `MPAlgorithm.state_eq_of_view`: after `t` rounds the state of a node only depends on its
  radius-`(t+1)` view (any graphs, possibly with cycles, possibly infinite);
* `MPAlgorithm.toAlgorithm`: an `r`-round message-passing algorithm defines a view-based algorithm
  with running time `r` on colour systems;
* `MPAlgorithm.ofView` / `out_ofView`: conversely, a view-based algorithm with running time `r` is
  computed by a full-information message-passing algorithm in `r` rounds, on every graph;
* `isMaximalMatching_view`: a view-based algorithm that is correct on all trees is correct on all
  graphs (outputs are lifted from the universal cover);
* `completion`: a **finite** simple edge-coloured graph whose view from a node agrees with a given
  colour system up to a given radius (and which is `d`-regular if the colour system is), so lower
  bounds proved with infinite trees also hold for finite graphs
  (`findsMaximalMatching_of_finite`).

## Related models

Edge colourings are the special case of port numberings in which both ends of an edge carry the
same port number; general port-numbered networks (independent port numbers at the two ends) need
a different covering theory. Locally-iterative algorithms with identifiers or colours are in
`Cslib.Computability.Distributed.Local`.

## References

* [J. Hirvonen, J. Suomela, *Distributed maximal matching: greedy is optimal*][HirvonenSuomela2012]
-/

@[expose] public section

namespace Cslib.ColourSystem

open FreeCox Pointwise

variable {k : ℕ}

namespace ColouredGraph

variable {α β : Type*} (G : ColouredGraph k α)

/-- The colours of the edges incident to `a`. -/
noncomputable def incident (a : α) : Finset (Fin k) := by
  classical exact Finset.univ.filter fun c => (G.step a c).isSome

theorem mem_incident {a : α} {c : Fin k} : c ∈ G.incident a ↔ (G.step a c).isSome := by
  classical simp [incident]

/-- A simple graph: no half-loops and at most one edge between any two nodes. Together with
`ColouredGraph.symm` this is a simple graph with a proper edge colouring by `Fin k`. -/
def IsSimple : Prop :=
  (∀ a c, G.step a c ≠ some a) ∧ ∀ a b c c', G.step a c = some b → G.step a c' = some b → c = c'

/-- Every node has degree `d`. -/
def IsRegular (d : ℕ) : Prop := ∀ a, (G.incident a).card = d

/-- `o` encodes a maximal matching of `G`: `o a = some c` means `a` is matched along its edge of
colour `c`, `o a = none` means `a` is unmatched. -/
def IsMaximalMatching (o : α → Option (Fin k)) : Prop :=
  ∀ a, (∀ c, o a = some c → (G.step a c).isSome) ∧
    (∀ c b, o a = some c → G.step a c = some b → o b = some c) ∧
    (o a = none → ∀ c b, G.step a c = some b → o b ≠ none)

theorem colours_view_one (a : α) (c : Fin k) :
    c ∈ colours (G.view a) 1 ↔ (G.step a c).isSome :=
  G.colours_view (G.walk_one a) c

theorem gen_mem_view {a : α} {c : Fin k} : gen c ∈ G.view a ↔ (G.step a c).isSome := by
  rw [← colours_view_one, mem_colours, one_mul]

/-- Neighbours of nodes with the same radius-`(R+1)` view have the same radius-`R` view. -/
theorem exists_step_of_ball_eq {H : ColouredGraph k β} {a : α} {b : β} {R : ℕ}
    (h : ball (G.view a) (R + 1) = ball (H.view b) (R + 1)) {c : Fin k} {a' : α}
    (ha : G.step a c = some a') :
    ∃ b', H.step b c = some b' ∧ ball (G.view a') R = ball (H.view b') R := by
  have h1 : gen c ∈ H.view b := by
    rw [← mem_iff_of_ball_eq h (by simp), G.gen_mem_view, ha]; rfl
  rw [H.gen_mem_view] at h1
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 h1
  refine ⟨b', hb', ?_⟩
  rw [← G.view_inv_smul (by rw [walk_gen]; exact ha),
    ← H.view_inv_smul (by rw [walk_gen]; exact hb')]
  exact ball_gen_inv_smul h c

theorem step_isSome_iff_of_ball_eq {H : ColouredGraph k β} {a : α} {b : β} {R : ℕ}
    (h : ball (G.view a) (R + 1) = ball (H.view b) (R + 1)) (c : Fin k) :
    (G.step a c).isSome ↔ (H.step b c).isSome := by
  rw [← G.gen_mem_view, ← H.gen_mem_view]
  exact mem_iff_of_ball_eq h (by simp)

end ColouredGraph

/-! ### Message-passing algorithms -/

/-- A deterministic synchronous message-passing algorithm for anonymous `k`-edge-coloured
networks. A node initially knows the set of its incident colours; the message sent along the edge
of colour `c` may depend on `c`; the received messages are indexed by the colour of the edge they
arrived on (`none` if there is no such edge). -/
structure MPAlgorithm (k : ℕ) where
  /-- Local states. -/
  State : Type
  /-- Messages. -/
  Msg : Type
  /-- The initial state of a node with the given set of incident colours. -/
  init : Finset (Fin k) → State
  /-- The message sent along the edge of colour `c`. -/
  send : State → Fin k → Msg
  /-- The new state, given the messages received along each colour (`none`: no such edge). -/
  recv : State → (Fin k → Option Msg) → State
  /-- The local output (for matchings: the colour of the matched edge, if any). -/
  output : State → Option (Fin k)

namespace MPAlgorithm

variable (M : MPAlgorithm k) {α β : Type*}

/-- The state of node `a` after `t` rounds. -/
noncomputable def state (G : ColouredGraph k α) : ℕ → α → M.State
  | 0, a => M.init (G.incident a)
  | t + 1, a => M.recv (state G t a) fun c => (G.step a c).map fun b => M.send (state G t b) c

/-- The output of node `a` after `r` rounds. -/
noncomputable def out (G : ColouredGraph k α) (r : ℕ) (a : α) : Option (Fin k) :=
  M.output (M.state G r a)

/-- After `t` rounds, the state of a node is determined by its radius-`(t+1)` view. -/
theorem state_eq_of_view {G : ColouredGraph k α} {H : ColouredGraph k β} (t : ℕ) :
    ∀ a b, ball (G.view a) (t + 1) = ball (H.view b) (t + 1) → M.state G t a = M.state H t b := by
  induction t with
  | zero =>
    intro a b h
    simp only [state]
    congr 1
    ext c
    rw [G.mem_incident, H.mem_incident]
    exact G.step_isSome_iff_of_ball_eq (R := 0) h c
  | succ t ih =>
    intro a b h
    simp only [state]
    rw [ih a b (ball_mono (by omega) h)]
    congr 1
    funext c
    have hiff := G.step_isSome_iff_of_ball_eq h c
    cases ha : G.step a c with
    | none =>
      cases hb : H.step b c with
      | none => rfl
      | some b' => rw [ha, hb] at hiff; simp at hiff
    | some a' =>
      obtain ⟨b', hb', hball⟩ := G.exists_step_of_ball_eq h ha
      rw [hb', Option.map_some, Option.map_some, ih a' b' hball]

theorem out_eq_of_view {G : ColouredGraph k α} {H : ColouredGraph k β} {r : ℕ} {a : α} {b : β}
    (h : ball (G.view a) (r + 1) = ball (H.view b) (r + 1)) : M.out G r a = M.out H r b := by
  simp only [out, M.state_eq_of_view r a b h]

/-! ### Colour systems as networks -/

open Classical in
/-- The edge-coloured tree `Γ_k(V)` as a network on the nodes of `V`. -/
noncomputable def gamma (V : Set (FreeCox k)) : ColouredGraph k V where
  step x c := if h : x.1 * gen c ∈ V then some ⟨x.1 * gen c, h⟩ else none
  symm a b c hab := by
    by_cases h : a.1 * gen c ∈ V
    · rw [dite_eq_left h] at hab
      cases hab
      simp only [mul_gen_mul_gen, a.2, dite_eq_left]
    · rw [dite_eq_right h] at hab; cases hab

theorem view_gamma {V : Set (FreeCox k)} (hV : IsColourSystem V) (x : V) :
    (gamma V).view x = x.1⁻¹ • V := by
  rw [← view_tGraph_empty hV x.2]
  refine ((gamma V).view_map (tGraph V fun _ => ∅) Subtype.val (fun a c => ?_) x).symm
  by_cases h : a.1 * gen c ∈ V
  · simp [gamma, tGraph, h, a.2]
  · simp [gamma, tGraph, h, a.2]

open Classical in
/-- An `r`-round message-passing algorithm as a view-based algorithm on colour systems. -/
noncomputable def toAlgorithm (r : ℕ) : Algorithm k := fun V v =>
  if hv : v ∈ V then M.out (gamma V) r ⟨v, hv⟩ else none

theorem toAlgorithm_of_mem {V : Set (FreeCox k)} {v : FreeCox k} (hv : v ∈ V) (r : ℕ) :
    M.toAlgorithm r V v = M.out (gamma V) r ⟨v, hv⟩ := by
  simp [toAlgorithm, hv]

/-- An `r`-round message-passing algorithm has running time `r` in the sense of §2.3. -/
theorem hasRunningTime_toAlgorithm (r : ℕ) : HasRunningTime (M.toAlgorithm r) r := by
  intro U V u v hU hV hu hv e
  rw [M.toAlgorithm_of_mem hu, M.toAlgorithm_of_mem hv]
  apply M.out_eq_of_view
  rw [view_gamma hU, view_gamma hV]
  exact e

/-- Correctness on the network `Γ_k(V)` is correctness on the colour system `V`. -/
theorem findsMaximalMatching_toAlgorithm {V : Set (FreeCox k)} (r : ℕ)
    (h : (gamma V).IsMaximalMatching (M.out (gamma V) r)) :
    FindsMaximalMatching (M.toAlgorithm r) V := by
  intro v hv
  obtain ⟨h1, h2, h3⟩ := h ⟨v, hv⟩
  rw [M.toAlgorithm_of_mem hv]
  have hstep : ∀ c (hc : v * gen c ∈ V), (gamma V).step ⟨v, hv⟩ c = some ⟨v * gen c, hc⟩ :=
    fun c hc => by simp [gamma, hc]
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun hn c hc => ?_⟩
  · have := h1 c hc
    by_contra hn
    rw [mem_colours] at hn
    simp [gamma, hn] at this
  · have hvc : v * gen c ∈ V := by
      by_contra hn
      have := h1 c hc
      simp [gamma, hn] at this
    rw [M.toAlgorithm_of_mem hvc]
    exact h2 c _ hc (hstep c hvc)
  · rw [mem_colours] at hc
    rw [M.toAlgorithm_of_mem hc]
    exact h3 hn c _ (hstep c hc)

/-! ### From views to message passing -/

theorem eq_one_or_gen_of_len_le_one {x : FreeCox k} (hx : len x ≤ 1) :
    x = 1 ∨ ∃ c, x = gen c := by
  rcases h : x.1 with _ | ⟨c, l⟩
  · exact Or.inl (FreeCox.ext h)
  · right
    have hl : l = [] := by
      have : x.1.length ≤ 1 := hx
      rw [h] at this
      simpa using this
    exact ⟨c, FreeCox.ext (by rw [h, hl]; rfl)⟩

theorem exists_startsWith {x : FreeCox k} (hx : x ≠ 1) : ∃ c, startsWith c x := by
  rcases h : x.1.getLast? with _ | c
  · exact absurd (FreeCox.ext (List.getLast?_eq_none_iff.1 h)) hx
  · exact ⟨c, (startsWith_iff c x).2 h⟩

/-- The full-information message-passing algorithm computing a view-based algorithm `A`: every
node forwards everything it knows; after `t` rounds it knows its radius-`(t+1)` view. -/
@[reducible] noncomputable def ofView (A : Algorithm k) : MPAlgorithm k where
  State := Set (FreeCox k)
  Msg := Set (FreeCox k)
  init C := insert 1 ((fun c => gen c) '' (C : Set (Fin k)))
  send s _ := s
  recv s m := s ∪ {x | ∃ c s', m c = some s' ∧ ∃ z ∈ s', x = gen c * z}
  output s := A s 1

theorem state_ofView (A : Algorithm k) (G : ColouredGraph k α) (t : ℕ) (a : α) :
    (ofView A).state G t a = ball (G.view a) (t + 1) := by
  induction t generalizing a with
  | zero =>
    refine Set.ext fun x => ?_
    simp only [state, Set.mem_insert_iff, Set.mem_image, Finset.mem_coe,
      G.mem_incident, mem_ball, zero_add]
    constructor
    · rintro (rfl | ⟨c, hc, rfl⟩)
      · exact ⟨G.one_mem_view a, by simp⟩
      · exact ⟨G.gen_mem_view.2 hc, by simp⟩
    · rintro ⟨hx, hx1⟩
      rcases eq_one_or_gen_of_len_le_one hx1 with rfl | ⟨c, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨c, G.gen_mem_view.1 hx, rfl⟩
  | succ t ih =>
    have e : ((ofView A).state G (t + 1) a : Set (FreeCox k)) =
        ((ofView A).state G t a : Set (FreeCox k)) ∪
        {x | ∃ c, ∃ s' : Set (FreeCox k),
          ((G.step a c).map fun b => ((ofView A).state G t b : Set (FreeCox k))) = some s' ∧
          ∃ z ∈ s', x = gen c * z} := rfl
    rw [e, ih]
    refine Set.ext fun x => ?_
    simp only [Set.mem_union, Set.mem_ofPred_eq, mem_ball]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨c, s', hs', z, hz, rfl⟩)
      · exact ⟨h1, by omega⟩
      · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hs'
        rw [ih] at hz
        obtain ⟨hz1, hz2⟩ := hz
        refine ⟨?_, by have := len_mul_le (gen c) z; simp at this; omega⟩
        rw [← G.view_inv_smul (by rw [ColouredGraph.walk_gen]; exact hb), mem_inv_smul] at hz1
        exact hz1
    · rintro ⟨h1, h2⟩
      by_cases hle : len x ≤ t + 1
      · exact Or.inl ⟨h1, hle⟩
      · right
        have hx1 : x ≠ 1 := by rintro rfl; simp at hle
        obtain ⟨c, hc⟩ := exists_startsWith hx1
        have hpre : IsPre (gen c) x := by
          unfold IsPre; rw [inv_gen, len_gen]
          have := le_len_gen_mul x c; unfold startsWith at hc; omega
        have hgc : gen c ∈ G.view a := (G.isColourSystem_view a).mem_of_isPre h1 hpre
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (G.gen_mem_view.1 hgc)
        refine ⟨c, (ofView A).state G t b, by rw [hb]; rfl, gen c * x, ?_,
          by rw [← mul_assoc, gen_mul_gen, one_mul]⟩
        rw [ih]
        refine ⟨?_, by unfold startsWith at hc; omega⟩
        rw [← G.view_inv_smul (by rw [ColouredGraph.walk_gen]; exact hb), mem_inv_smul, ← mul_assoc,
          gen_mul_gen, one_mul]
        exact h1

/-- A view-based algorithm with running time `r` is computed by the full-information
message-passing algorithm in `r` rounds, on every network. -/
theorem out_ofView {A : Algorithm k} {r : ℕ} (hA : HasRunningTime A r) (G : ColouredGraph k α)
    (a : α) : (ofView A).out G r a = A (G.view a) 1 := by
  simp only [out, state_ofView]
  show A _ 1 = _
  have hV := G.isColourSystem_view a
  exact hA.apply_one_eq (hV.ball _) hV (ball_ball _ _)

/-- Lifting from the universal cover: an algorithm with running time `r` that finds a maximal
matching in every colour system finds a maximal matching in every edge-coloured network. -/
theorem isMaximalMatching_view {A : Algorithm k} {r : ℕ} (hA : HasRunningTime A r)
    (hMM : ∀ V, IsColourSystem V → FindsMaximalMatching A V) (G : ColouredGraph k α) :
    G.IsMaximalMatching fun a => A (G.view a) 1 := by
  intro a
  have hV := G.isColourSystem_view a
  obtain ⟨m1, m2, m3⟩ := hMM _ hV 1 hV.one_mem
  have hnb : ∀ c b, G.step a c = some b → A (G.view a) (1 * gen c) = A (G.view b) 1 := by
    intro c b hb
    have hw : G.walk a (gen c) = some b := by rw [ColouredGraph.walk_gen]; exact hb
    rw [one_mul, hA.apply_eq hV (G.mem_view.2 ⟨b, hw⟩), G.view_inv_smul hw]
  refine ⟨fun c hc => (G.colours_view_one a c).1 (m1 c hc), fun c b hc hb => ?_,
    fun hn c b hb => ?_⟩
  · change A (G.view b) 1 = some c
    rw [← hnb c b hb]; exact m2 c hc
  · change A (G.view b) 1 ≠ none
    rw [← hnb c b hb]
    exact m3 hn c ((G.colours_view_one a c).2 (by rw [hb]; rfl))

/-! ### Finite completions -/

open Classical in
/-- A finite network realising the radius-`R` ball of `V`: `2^k` copies of the finite tree
`V[R]`; a node `x` of a copy that lacks the edge of colour `c` present in `V` (`x c ∈ V \ V[R]`)
is joined by colour `c` to its twin in the copy obtained by flipping coordinate `c`. -/
noncomputable def completion (V : Set (FreeCox k)) (R : ℕ) :
    ColouredGraph k (ball V R × (Fin k → Bool)) where
  step p c :=
    if h : p.1.1 * gen c ∈ ball V R then some (⟨p.1.1 * gen c, h⟩, p.2)
    else if p.1.1 * gen c ∈ V then some (p.1, Function.update p.2 c (!p.2 c)) else none
  symm p q c hpq := by
    by_cases h1 : p.1.1 * gen c ∈ ball V R
    · rw [dite_eq_left h1] at hpq
      cases hpq
      simp [p.1.2]
    · rw [dite_eq_right h1] at hpq
      by_cases h2 : p.1.1 * gen c ∈ V
      · rw [ite_eq_left h2] at hpq
        cases hpq
        simp [h1, h2]
      · rw [ite_eq_right h2] at hpq; cases hpq

section completion

variable {V : Set (FreeCox k)} {R : ℕ}

instance finite_completion_nodes : Finite (ball V R × (Fin k → Bool)) := by
  have : Finite (ball V R) := (ball_finite V R).to_subtype
  infer_instance

theorem completion_step_isSome (p : ball V R × (Fin k → Bool)) (c : Fin k) :
    ((completion V R).step p c).isSome ↔ p.1.1 * gen c ∈ V := by
  by_cases h1 : p.1.1 * gen c ∈ ball V R
  · simp only [completion, dite_eq_left h1, Option.isSome_some, true_iff]; exact h1.1
  · by_cases h2 : p.1.1 * gen c ∈ V <;> simp [completion, h1, h2]

theorem completion_isSimple : (completion V R).IsSimple := by
  constructor
  · intro p c h
    simp only [completion] at h
    split_ifs at h with h1 h2 <;> simp only [Option.some.injEq] at h
    · have := congrArg (fun q => q.1.1) h
      simp only at this
      exact gen_ne_one c (by simpa using congrArg (p.1.1⁻¹ * ·) this)
    · have := congrFun (congrArg Prod.snd h) c
      simp at this
  · intro p q c c' h h'
    simp only [completion] at h h'
    split_ifs at h h' with h1 h2 h3 h4 h3 h4 <;> cases h <;> simp only [Option.some.injEq] at h'
    · have := congrArg (fun q => q.1.1) h'
      simp only at this
      exact gen_injective (mul_left_cancel this).symm
    · have := congrArg (fun q => q.1.1) h'
      simp only at this
      exact (gen_ne_one c (by
        have := congrArg (p.1.1⁻¹ * ·) this; simp at this; exact this.symm)).elim
    · have := congrArg (fun q => q.1.1) h'
      simp only at this
      exact (gen_ne_one c' (by
        have := congrArg (p.1.1⁻¹ * ·) this
        simp only [inv_mul_cancel_left, inv_mul_cancel] at this
        exact this)).elim
    · by_contra hne
      have := congrFun (congrArg Prod.snd h') c
      simp [Function.update_of_ne hne] at this

theorem completion_isRegular {d : ℕ} (hV : IsRegular V d) :
    (completion V R).IsRegular d := by
  intro p
  rw [← hV p.1.1 p.1.2.1]
  congr 1
  ext c
  rw [ColouredGraph.mem_incident, completion_step_isSome, mem_colours]

/-- The completion's view from the root agrees with `V` up to radius `R`. -/
theorem ball_view_completion (hV : IsColourSystem V) (s : Fin k → Bool) :
    ball ((completion V R).view (⟨1, hV.one_mem, by simp⟩, s)) R = ball V R := by
  classical
  have h1R : (1 : FreeCox k) ∈ ball V R := ⟨hV.one_mem, by simp⟩
  let f : FreeCox k → ball V R × (Fin k → Bool) := fun x =>
    if hx : x ∈ ball V R then (⟨x, hx⟩, s) else (⟨1, h1R⟩, s)
  have hf1 : f 1 = (⟨1, hV.one_mem, by simp⟩, s) := by simp [f]
  rw [← hf1, (tGraph V fun _ => ∅).ball_view_map_le (completion V R) f 1 R ?_,
    view_tGraph_empty hV hV.one_mem, inv_one, one_smul]
  intro x b hx hb c
  rw [walk_tGraph_empty hV hV.one_mem, one_mul] at hb
  split_ifs at hb with hxV
  cases hb
  have hbR : x ∈ ball V R := ⟨hxV, by omega⟩
  have hfx : f x = (⟨x, hbR⟩, s) := by simp only [f, dite_eq_left hbR]
  rw [hfx]
  by_cases hc : x * gen c ∈ V
  · have hcR : x * gen c ∈ ball V R := ⟨hc, by have := len_mul_gen_le x c; omega⟩
    rw [tGraph_step_of_mem hxV hc, Option.map_some]
    simp only [completion, dite_eq_left hcR, f]
  · rw [tGraph_step_of_not_mem hxV hc (by simp), Option.map_none]
    have hcR : x * gen c ∉ ball V R := fun h => hc h.1
    simp only [completion, dite_eq_right hcR, ite_eq_right hc]

end completion

/-- **Finite graphs suffice.** If an `r`-round message-passing algorithm finds a maximal matching
in every finite simple `k`-edge-coloured network [that is `d`-regular], then the corresponding
view-based algorithm finds a maximal matching in every [`d`-regular] colour system. -/
theorem findsMaximalMatching_of_finite (r : ℕ) (P : ℕ → Prop)
    (hfin : ∀ (α : Type) [Finite α] (G : ColouredGraph k α), G.IsSimple →
      (∀ d, P d → G.IsRegular d) → G.IsMaximalMatching (M.out G r))
    {V : Set (FreeCox k)} (hV : IsColourSystem V) (hreg : ∀ d, P d → IsRegular V d) :
    FindsMaximalMatching (M.toAlgorithm r) V := by
  intro v hv
  set W := v⁻¹ • V
  have hW : IsColourSystem W := hV.inv_smul hv
  set H := completion W (r + 2)
  set s : Fin k → Bool := fun _ => false
  set h0 : ball W (r + 2) × (Fin k → Bool) := (⟨1, hW.one_mem, by simp⟩, s)
  have hball : ball (H.view h0) (r + 2) = ball W (r + 2) := ball_view_completion hW s
  obtain ⟨m1, m2, m3⟩ := hfin _ H completion_isSimple
    (fun d hd => completion_isRegular (isRegular_inv_smul (hreg d hd) v)) h0
  have hgv : (gamma V).view ⟨v, hv⟩ = W := view_gamma hV _
  -- outputs at `v` and its neighbours are those of `h0` and its neighbours
  have hout0 : M.toAlgorithm r V v = M.out H r h0 := by
    rw [M.toAlgorithm_of_mem hv]
    apply M.out_eq_of_view
    rw [hgv, ball_mono (by omega) hball]
  have hnb : ∀ c, v * gen c ∈ V → ∃ h1, H.step h0 c = some h1 ∧
      M.toAlgorithm r V (v * gen c) = M.out H r h1 := by
    intro c hc
    have hstep : (gamma V).step ⟨v, hv⟩ c = some ⟨v * gen c, hc⟩ := by simp [gamma, hc]
    have e : ball ((gamma V).view ⟨v, hv⟩) (r + 1 + 1) = ball (H.view h0) (r + 1 + 1) := by
      rw [hgv, hball]
    obtain ⟨h1, hh1, hb⟩ := (gamma V).exists_step_of_ball_eq e hstep
    exact ⟨h1, hh1, by rw [M.toAlgorithm_of_mem hc]; exact M.out_eq_of_view hb⟩
  have hcol : ∀ c, (H.step h0 c).isSome ↔ v * gen c ∈ V := by
    intro c
    rw [completion_step_isSome]
    simp [h0, W, mem_inv_smul]
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun hn c hc => ?_⟩
  · rw [hout0] at hc
    exact mem_colours.2 ((hcol c).1 (m1 c hc))
  · rw [hout0] at hc
    obtain ⟨h1, hh1, he⟩ := hnb c ((hcol c).1 (m1 c hc))
    rw [he]
    exact m2 c h1 hc hh1
  · rw [hout0] at hn
    obtain ⟨h1, hh1, he⟩ := hnb c (mem_colours.1 hc)
    rw [he]
    exact m3 hn c h1 hh1

end MPAlgorithm

end Cslib.ColourSystem
