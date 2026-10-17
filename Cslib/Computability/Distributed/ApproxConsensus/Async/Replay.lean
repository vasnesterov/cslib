/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.ApproxConsensus.Async.Model
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Linarith

/-!
# Replaying executions on a node set

The indistinguishability tool of the impossibility proofs in the asynchronous digraph model
(`Cslib.Computability.Distributed.ApproxConsensus.Async.Model`). `proj R B' C e` turns an event `e`
of a *source* execution into an event of a *target* execution that replays the deliveries into the
node set `R`; deliveries from senders that are faulty in the target become `byz` events.

* `Agree R C C'` / `AgreeOut R C C'`: configurations agree on (outside) `R`.
* `sim_phase`: if every in-neighbour of `R` outside `R` is faulty in the source (hence silent)
  or in the target (hence simulable), a replay phase preserves agreement on `R` and changes
  nothing outside `R`.
* `exists_replay₂`: two replay phases on disjoint node sets yield one target execution that is
  indistinguishable, on each set, from the corresponding source execution.
* `roundRobin`: a fair schedule without `byz` events.
-/

@[expose] public section

open Finset

namespace Cslib.ApproxConsensus.Async

variable {V M S : Type*} [DecidableEq V] {A : Algorithm V M S} {G : Digraph V} [DecidableRel G.Adj]

/-- Two configurations agree on the node set `R`: states, decisions, and the channels inside `R`. -/
def Agree (R : Finset V) (C C' : Config V M S) : Prop :=
  (∀ y ∈ R, C.st y = C'.st y ∧ C.dec y = C'.dec y) ∧ ∀ x ∈ R, ∀ y ∈ R, C.chan x y = C'.chan x y

/-- Two configurations agree outside `R`. -/
def AgreeOut (R : Finset V) (C C' : Config V M S) : Prop :=
  (∀ y ∉ R, C.st y = C'.st y ∧ C.dec y = C'.dec y) ∧ ∀ x ∉ R, ∀ y ∉ R, C.chan x y = C'.chan x y

omit [DecidableEq V] in
/-- Agreement outside `R` is reflexive. -/
theorem AgreeOut.refl {R : Finset V} (C : Config V M S) : AgreeOut R C C :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl⟩

omit [DecidableEq V] in
/-- Agreement outside `R` is transitive. -/
theorem AgreeOut.trans {R : Finset V} {C₁ C₂ C₃ : Config V M S} (h₁ : AgreeOut R C₁ C₂)
    (h₂ : AgreeOut R C₂ C₃) : AgreeOut R C₁ C₃ :=
  ⟨fun y hy => ⟨(h₁.1 y hy).1.trans (h₂.1 y hy).1, (h₁.1 y hy).2.trans (h₂.1 y hy).2⟩,
    fun x hx y hy => (h₁.2 x hx y hy).trans (h₂.2 x hx y hy)⟩

omit [DecidableEq V] in
/-- Agreement on `R'` is transported along agreement outside `R` when `R' ∩ R = ∅`. -/
theorem Agree.of_agreeOut {R R' : Finset V} {C C₁ C₂ : Config V M S} (h : Agree R' C C₁)
    (h' : AgreeOut R C₁ C₂) (hd : Disjoint R' R) : Agree R' C C₂ :=
  ⟨fun y hy => ⟨(h.1 y hy).1.trans (h'.1 y (disjoint_left.mp hd hy)).1,
      (h.1 y hy).2.trans (h'.1 y (disjoint_left.mp hd hy)).2⟩,
    fun x hx y hy => (h.2 x hx y hy).trans (h'.2 x (disjoint_left.mp hd hx) y
      (disjoint_left.mp hd hy))⟩

/-- The event of the target execution simulating the source event `e` (from configuration `C`)
on the node set `R`: deliveries into `R` are replayed, those from Byzantine (in the target)
senders are injected by the adversary; everything else is skipped. -/
def proj (R B' : Finset V) (C : Config V M S) : Event V M → Event V M
  | .deliver x y =>
    if y ∈ R then
      match C.chan x y with
      | [] => .skip
      | m :: _ => if x ∈ B' then .byz x y m else .deliver x y
    else .skip
  | _ => .skip

/-- Source invariant: only correct nodes have non-empty channels, and only along links. -/
def ChanOK (G : Digraph V) (B : Finset V) (C : Config V M S) : Prop :=
  ∀ x y, C.chan x y ≠ [] → x ∉ B ∧ G.Adj x y ∧ x ≠ y

/-- Messages are only put on links of `G` between distinct nodes towards correct nodes. -/
theorem sendTo_ne_nil {B : Finset V} {y b : V} {outs : List (V × M)}
    (h : sendTo G B y outs b ≠ []) : b ∉ B ∧ G.Adj y b ∧ y ≠ b := by
  unfold sendTo at h; split_ifs at h with h'
  · exact h'
  · exact absurd rfl h

/-- Processing a message by a correct node preserves `ChanOK`. -/
theorem chanOK_process {B : Finset V} {C : Config V M S} (hC : ChanOK G B C) {y x : V} {m : M}
    (hy : y ∉ B) : ChanOK G B (process A G B C y x m) := by
  intro a b h
  simp only [process] at h
  split_ifs at h with hay
  · subst hay
    by_cases h1 : C.chan a b = []
    · rw [h1, List.nil_append] at h
      exact ⟨hy, (sendTo_ne_nil h).2⟩
    · exact hC a b h1
  · exact hC a b h

omit [DecidableRel G.Adj] in
/-- Removing the head of a channel preserves `ChanOK`. -/
theorem chanOK_pop {B : Finset V} {C : Config V M S} (hC : ChanOK G B C) {x y : V} {m : M}
    {rest : List M} (hxy : C.chan x y = m :: rest) : ChanOK G B (C.pop x y rest) := by
  intro a b h
  simp only [Config.pop] at h
  split_ifs at h with hab
  · obtain ⟨rfl, rfl⟩ := hab; exact hC a b (by simp [hxy])
  · exact hC a b h

/-- Every step preserves `ChanOK`. -/
theorem chanOK_step {B : Finset V} {C : Config V M S} (hC : ChanOK G B C) (e : Event V M) :
    ChanOK G B (step A G B C e) := by
  cases e with
  | deliver x y =>
    simp only [step]
    split
    · exact hC
    · rename_i m rest hxy
      split_ifs with hy
      · exact hC
      · exact chanOK_process (chanOK_pop hC hxy) hy
  | byz x y m =>
    simp only [step]
    split_ifs with h
    · exact chanOK_process hC h.2.1
    · exact hC
  | skip => exact hC

/-- The initial configuration satisfies `ChanOK`. -/
theorem chanOK_init {B : Finset V} (inp : V → ℝ) : ChanOK G B (init A G B inp) := by
  intro x y h
  simp only [init] at h
  split_ifs at h with hx
  · exact absurd rfl h
  · exact ⟨hx, (sendTo_ne_nil h).2⟩

/-- Every configuration of a run satisfies `ChanOK`. -/
theorem chanOK_run {B : Finset V} (inp : V → ℝ) (ev : ℕ → Event V M) (t : ℕ) :
    ChanOK G B (run A G B inp ev t) := by
  induction t with
  | zero => exact chanOK_init inp
  | succ t ih => exact chanOK_step ih _

section Sim

variable {B B' R : Finset V}

/-- Processing the same message at a node of `R` preserves agreement on `R`. -/
theorem agree_process (hRB : ∀ y ∈ R, y ∉ B) (hRB' : ∀ y ∈ R, y ∉ B') {C C' : Config V M S}
    (h : Agree R C C') {y x : V} (hy : y ∈ R) (m : M) :
    Agree R (process A G B C y x m) (process A G B' C' y x m) := by
  have hst := (h.1 y hy).1
  refine ⟨fun z hz => ?_, fun a ha b hb => ?_⟩
  · by_cases hzy : z = y
    · subst hzy; simp [process, hst, (h.1 z hz).2]
    · simp [process, hzy, (h.1 z hz).1, (h.1 z hz).2]
  · simp only [process]
    split_ifs with hay
    · subst hay
      rw [h.2 a ha b hb, hst]
      congr 1
      simp only [sendTo, hRB b hb, hRB' b hb, not_false_eq_true, true_and]
    · exact h.2 a ha b hb

/-- Processing a message at a node of `R` changes nothing outside `R`. -/
theorem agreeOut_process {C : Config V M S} {y x : V} (hy : y ∈ R) (m : M) :
    AgreeOut R C (process A G B' C y x m) := by
  refine ⟨fun z hz => ?_, fun a ha b _ => ?_⟩
  · have : z ≠ y := fun h => hz (h ▸ hy)
    simp [process, this]
  · have : a ≠ y := fun h => ha (h ▸ hy)
    simp [process, this]

/-- Popping a channel whose sender is outside `R` (in the second configuration) preserves
agreement on `R`. -/
theorem agree_pop_right {C C' : Config V M S} (h : Agree R C C') {x y : V} (hy : x ∉ R)
    (rest : List M) : Agree R C (C'.pop x y rest) :=
  ⟨h.1, fun a ha b hb => by
    have : ¬ (a = x ∧ b = y) := fun h' => hy (h'.1 ▸ ha)
    simp [Config.pop, this, h.2 a ha b hb]⟩

/-- Popping a channel whose sender is outside `R` (in the first configuration) preserves
agreement on `R`. -/
theorem agree_pop_left {C C' : Config V M S} (h : Agree R C C') {x y : V} (hy : x ∉ R)
    (rest : List M) : Agree R (C.pop x y rest) C' :=
  ⟨h.1, fun a ha b hb => by
    have : ¬ (a = x ∧ b = y) := fun h' => hy (h'.1 ▸ ha)
    simp [Config.pop, this, h.2 a ha b hb]⟩

/-- One simulation step: the source executes a non-Byzantine event, the target executes its
projection on `R`. Agreement on `R` is preserved, provided every in-neighbour of `R` outside `R`
is Byzantine in the source (hence silent) or in the target (hence simulable). -/
theorem agree_step (hRB : ∀ y ∈ R, y ∉ B) (hRB' : ∀ y ∈ R, y ∉ B')
    (hcl : ∀ x y, G.Adj x y → x ≠ y → y ∈ R → x ∉ R → x ∈ B ∨ x ∈ B')
    {C C' : Config V M S} (hC : ChanOK G B C) (h : Agree R C C') (e : Event V M)
    (he : ∀ x y m, e ≠ .byz x y m) :
    Agree R (step A G B C e) (step A G B' C' (proj R B' C e)) := by
  cases e with
  | byz x y m => exact absurd rfl (he x y m)
  | skip => exact h
  | deliver x y =>
    by_cases hy : y ∈ R
    · simp only [proj, hy, ite_true]
      rcases hxy : C.chan x y with _ | ⟨m, rest⟩
      · simp only [step, hxy]; exact h
      · have hyB : y ∉ B := hRB y hy
        have hyB' : y ∉ B' := hRB' y hy
        simp only [step, hxy, hyB, ite_false]
        by_cases hx : x ∈ R
        · have hxB' : x ∉ B' := hRB' x hx
          simp only [hxB', ite_false, ← h.2 x hx y hy, hxy, hyB', ite_false]
          apply agree_process hRB hRB' _ hy
          exact ⟨h.1, fun a ha b hb => by
            simp only [Config.pop]
            split_ifs
            · rfl
            · exact h.2 a ha b hb⟩
        · obtain ⟨hxB, hadj, hne⟩ := hC x y (by simp [hxy])
          have hxB' : x ∈ B' := (hcl x y hadj hne hy hx).resolve_left hxB
          simp only [hxB', ite_true, hyB', not_false_eq_true, hadj, ne_eq, hne,
            and_self, ite_true]
          exact agree_process hRB hRB' (agree_pop_left h hx rest) hy m
    · simp only [proj, hy, ite_false, step]
      refine ⟨fun z hz => ?_, fun a ha b hb => ?_⟩
      · split
        · exact h.1 z hz
        · split_ifs
          · exact h.1 z hz
          · have hzy : z ≠ y := fun h' => hy (h' ▸ hz)
            simp [process, Config.pop, hzy, h.1 z hz]
      · split
        · exact h.2 a ha b hb
        · split_ifs
          · exact h.2 a ha b hb
          · have hay : a ≠ y := fun h' => hy (h' ▸ ha)
            have hby : ¬ (a = x ∧ b = y) := fun h' => hy (h'.2 ▸ hb)
            simp [process, Config.pop, hay, hby, h.2 a ha b hb]

/-- The projected target step changes nothing outside `R`. -/
theorem agreeOut_step_proj {C C' : Config V M S} (e : Event V M) :
    AgreeOut R C' (step A G B' C' (proj R B' C e)) := by
  cases e with
  | byz => exact AgreeOut.refl _
  | skip => exact AgreeOut.refl _
  | deliver x y =>
    by_cases hy : y ∈ R
    · simp only [proj, hy, ite_true]
      rcases C.chan x y with _ | ⟨m, rest⟩
      · exact AgreeOut.refl _
      · split_ifs with hx
        · simp only [step]
          split_ifs
          · exact agreeOut_process hy m
          · exact AgreeOut.refl _
        · simp only [step]
          split
          · exact AgreeOut.refl _
          · split_ifs
            · exact AgreeOut.refl _
            · rename_i m' rest' _ _
              refine AgreeOut.trans (C₂ := C'.pop x y rest')
                ⟨fun z _ => ⟨rfl, rfl⟩, fun a _ b hb => ?_⟩ (agreeOut_process hy m')
              have : ¬ (a = x ∧ b = y) := fun h' => hb (h'.2 ▸ hy)
              simp [Config.pop, this]
    · simp only [proj, hy, ite_false]; exact AgreeOut.refl _

/-- A whole simulation phase: if the target events at times `T₀ + k` (`k < K`) are the
projections of the source events, agreement on `R` propagates from time `0`/`T₀` to `K`/`T₀+K`,
and nothing outside `R` changes in the target. -/
theorem sim_phase (hRB : ∀ y ∈ R, y ∉ B) (hRB' : ∀ y ∈ R, y ∉ B')
    (hcl : ∀ x y, G.Adj x y → x ≠ y → y ∈ R → x ∉ R → x ∈ B ∨ x ∈ B')
    (inp inp' : V → ℝ) (ev ev' : ℕ → Event V M) (hev : ∀ t x y m, ev t ≠ .byz x y m)
    (T₀ K : ℕ) (hproj : ∀ k < K, ev' (T₀ + k) = proj R B' (run A G B inp ev k) (ev k))
    (h0 : Agree R (run A G B inp ev 0) (run A G B' inp' ev' T₀)) :
    Agree R (run A G B inp ev K) (run A G B' inp' ev' (T₀ + K)) ∧
      AgreeOut R (run A G B' inp' ev' T₀) (run A G B' inp' ev' (T₀ + K)) := by
  induction K with
  | zero => exact ⟨h0, AgreeOut.refl _⟩
  | succ K ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k hk => hproj k (by omega)
    have e := hproj K (by omega)
    have hrun : run A G B' inp' ev' (T₀ + (K + 1)) =
        step A G B' (run A G B' inp' ev' (T₀ + K)) (ev' (T₀ + K)) := rfl
    rw [hrun, e]
    exact ⟨agree_step hRB hRB' hcl (chanOK_run inp ev K) ih1 (ev K) (hev K),
      ih2.trans (agreeOut_step_proj _)⟩

end Sim

/-- Round-robin delivery over all ordered pairs: a fair schedule without Byzantine events. -/
noncomputable def roundRobin [Fintype V] : ℕ → Event V M := fun t =>
  let e := (Fintype.equivFin (V × V)).symm
  let N := Fintype.card (V × V)
  if h : 0 < N then
    let p := e ⟨t % N, Nat.mod_lt _ h⟩
    .deliver p.1 p.2
  else .skip

/-- The round-robin schedule is fair. -/
theorem roundRobin_fair [Fintype V] {B : Finset V} (inp : V → ℝ) :
    Fair A G B inp (roundRobin (V := V) (M := M)) := by
  intro x y _ _ t _
  have hN : 0 < Fintype.card (V × V) := Fintype.card_pos_iff.mpr ⟨(x, y)⟩
  set i := (Fintype.equivFin (V × V) (x, y)).val
  have hi : i < Fintype.card (V × V) := (Fintype.equivFin (V × V) (x, y)).isLt
  refine ⟨Fintype.card (V × V) * t + i, by nlinarith, ?_⟩
  have hmod : (Fintype.card (V × V) * t + i) % Fintype.card (V × V) = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have h' : (Fintype.equivFin (V × V)).symm
      ⟨(Fintype.card (V × V) * t + i) % Fintype.card (V × V), Nat.mod_lt _ hN⟩ = (x, y) := by
    rw [Equiv.symm_apply_eq]; exact Fin.ext hmod
  simp only [roundRobin, hN, ↓reduceDIte, h']

omit [DecidableEq V] in
/-- The round-robin schedule has no `byz` events. -/
theorem roundRobin_ne_byz [Fintype V] (t : ℕ) (x y : V) (m : M) :
    roundRobin (V := V) (M := M) t ≠ .byz x y m := by
  simp only [roundRobin]; split <;> simp

/-- Projected events are `byz` events only for senders that are faulty in the target. -/
theorem mem_of_proj_eq_byz {R B' : Finset V} {C : Config V M S} {e : Event V M} {x y : V} {m : M}
    (h : proj R B' C e = .byz x y m) : x ∈ B' := by
  cases e with
  | deliver a b =>
    unfold proj at h
    by_cases hb : b ∈ R <;> simp only [hb, ite_true, ite_false] at h
    · rcases hc : C.chan a b with _ | ⟨m', rest⟩ <;> simp only [hc] at h
      · cases h
      · by_cases ha : a ∈ B' <;> simp only [ha, ite_true, ite_false] at h
        · cases h; exact ha
        · cases h
    · cases h
  | byz => cases h
  | skip => cases h

/-- **Two-phase replay.** Let `R₁, R₂` be disjoint node sets such that every in-neighbour of `Rᵢ`
outside `Rᵢ` is faulty in the source execution `eᵢ = run A G Bᵢ inpᵢ evᵢ` (which has no `byz`
events) or in the target. If the target inputs agree with `inpᵢ` on `Rᵢ`, some target event
sequence (whose `byz` events all come from target-faulty senders) reaches, at time `T₁ + T₂`, a
configuration agreeing with `e₁` at time `T₁` on `R₁` and with `e₂` at time `T₂` on `R₂`. -/
theorem exists_replay₂ {B₁ B₂ B R₁ R₂ : Finset V} (hR : Disjoint R₁ R₂)
    (hR₁ : ∀ y ∈ R₁, y ∉ B₁ ∧ y ∉ B) (hR₂ : ∀ y ∈ R₂, y ∉ B₂ ∧ y ∉ B)
    (hcl₁ : ∀ x y, G.Adj x y → x ≠ y → y ∈ R₁ → x ∉ R₁ → x ∈ B₁ ∨ x ∈ B)
    (hcl₂ : ∀ x y, G.Adj x y → x ≠ y → y ∈ R₂ → x ∉ R₂ → x ∈ B₂ ∨ x ∈ B)
    {inp₁ inp₂ inp : V → ℝ} (hinp₁ : ∀ y ∈ R₁, inp y = inp₁ y) (hinp₂ : ∀ y ∈ R₂, inp y = inp₂ y)
    {ev₁ ev₂ : ℕ → Event V M} (hev₁ : ∀ t x y m, ev₁ t ≠ .byz x y m)
    (hev₂ : ∀ t x y m, ev₂ t ≠ .byz x y m) (T₁ T₂ : ℕ) :
    ∃ ev : ℕ → Event V M, (∀ t x y m, ev t = .byz x y m → x ∈ B) ∧
      Agree R₁ (run A G B₁ inp₁ ev₁ T₁) (run A G B inp ev (T₁ + T₂)) ∧
      Agree R₂ (run A G B₂ inp₂ ev₂ T₂) (run A G B inp ev (T₁ + T₂)) := by
  set ev : ℕ → Event V M := fun t =>
    if t < T₁ then proj R₁ B (run A G B₁ inp₁ ev₁ t) (ev₁ t)
    else if t < T₁ + T₂ then proj R₂ B (run A G B₂ inp₂ ev₂ (t - T₁)) (ev₂ (t - T₁))
    else .skip
  have h0 : ∀ {Bᵢ Rᵢ : Finset V} {inpᵢ : V → ℝ} {evᵢ : ℕ → Event V M},
      (∀ y ∈ Rᵢ, y ∉ Bᵢ ∧ y ∉ B) → (∀ y ∈ Rᵢ, inp y = inpᵢ y) →
      Agree Rᵢ (run A G Bᵢ inpᵢ evᵢ 0) (run A G B inp ev 0) := by
    intro Bᵢ Rᵢ inpᵢ evᵢ hRᵢ hinpᵢ
    refine ⟨fun y hy => ?_, fun x hx y hy => ?_⟩
    · simp [run, init, hinpᵢ y hy]
    · simp [run, init, sendTo, hinpᵢ x hx, (hRᵢ x hx).1, (hRᵢ x hx).2, (hRᵢ y hy).1,
        (hRᵢ y hy).2]
  refine ⟨ev, fun t x y m h => ?_, ?_⟩
  · simp only [ev] at h
    split_ifs at h
    · exact mem_of_proj_eq_byz h
    · exact mem_of_proj_eq_byz h
  obtain ⟨p1a, p1b⟩ := sim_phase (A := A) (fun y hy => (hR₁ y hy).1) (fun y hy => (hR₁ y hy).2)
    hcl₁ inp₁ inp ev₁ ev hev₁ 0 T₁ (fun k hk => by simp only [ev, Nat.zero_add, hk, ite_true])
    (by simpa using h0 hR₁ hinp₁)
  obtain ⟨p2a, p2b⟩ := sim_phase (A := A) (fun y hy => (hR₂ y hy).1) (fun y hy => (hR₂ y hy).2)
    hcl₂ inp₂ inp ev₂ ev hev₂ T₁ T₂
    (fun k hk => by
      simp only [ev, show ¬ (T₁ + k < T₁) by omega, ite_false,
        show T₁ + k < T₁ + T₂ by omega, ite_true, Nat.add_sub_cancel_left])
    ((h0 hR₂ hinp₂).of_agreeOut (by simpa using p1b) hR.symm)
  exact ⟨(by simpa using p1a : Agree R₁ _ _).of_agreeOut p2b hR, p2a⟩

end Cslib.ApproxConsensus.Async
