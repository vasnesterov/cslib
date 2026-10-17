/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.ContentOblivious.Model

/-!
# Histories, solitude runs and lockstep executions on oriented rings

A deterministic content-oblivious node is determined by its ID and the sequence of ports at which
it has consumed pulses (its *history*, oldest first; `false` = `Port0`, i.e. a CW pulse on an
oriented ring). `run A i w` is its state and the number of pulses it has sent on each port after
history `w`.

* `Ok A i w d`: a node with ID `i` and history `w` that is alone on a ring (a 1-node ring, where its
  `Port1` is linked to its own `Port0`) can consume a pulse at port `d`.
* `Valid A i w`: every step of `w` is `Ok`; such `w` are exactly the histories of solitude runs
  (`reach_one_iff`).
* `reach_sync` (*lockstep / indistinguishability lemma*): if a history `w` is valid in solitude for
  every node of an oriented ring, then the configuration in which every node has history `w` is
  reachable. The scheduler delivers pulses round by round, the `k`-th round delivering to every
  node a pulse at port `w[k]`.
-/

@[expose] public section

namespace Cslib.ContentOblivious

open Finset

variable (A : Algo)

/-- State and cumulative numbers of pulses sent per port after history `w`. -/
def run (i : ℕ) (w : List Bool) : A.State × (Bool → ℕ) :=
  w.foldl (fun r d => ((A.recv r.1 d).1, fun p => r.2 p + (A.recv r.1 d).2 p)) (A.init i)

/-- The empty history is the initial state. -/
@[simp] lemma run_nil (i : ℕ) : run A i [] = A.init i := rfl

/-- Extending the history by one reception. -/
lemma run_append (i : ℕ) (w : List Bool) (d : Bool) :
    run A i (w ++ [d]) = ((A.recv (run A i w).1 d).1,
      fun p => (run A i w).2 p + (A.recv (run A i w).1 d).2 p) := by
  simp [run, List.foldl_append]

/-- In solitude, the node with ID `i` and history `w` can consume a pulse at port `d`
(pulses arriving at port `d` were sent by the node itself on port `!d`). -/
def Ok (i : ℕ) (w : List Bool) (d : Bool) : Prop :=
  A.terminated (run A i w).1 = false ∧ A.ready (run A i w).1 d = true ∧
    w.count d < (run A i w).2 (!d)

/-- A history that is realizable in solitude. -/
def Valid (i : ℕ) (w : List Bool) : Prop := ∀ u d, (u ++ [d]) <+: w → Ok A i u d

variable {A}

/-- The empty history is valid. -/
lemma Valid.nil (i : ℕ) : Valid A i [] := by
  intro u d h
  have := h.length_le; simp at this

/-- Prefixes of valid histories are valid. -/
lemma Valid.of_prefix {i : ℕ} {w w' : List Bool} (h : Valid A i w') (hw : w <+: w') : Valid A i w :=
  fun u d hu => h u d (hu.trans hw)

/-- Extending a valid history by an allowed reception. -/
lemma Valid.append {i : ℕ} {w : List Bool} {d : Bool} (h : Valid A i w) (hd : Ok A i w d) :
    Valid A i (w ++ [d]) := by
  intro u e hu
  rcases List.prefix_concat_iff.1 hu with heq | hp
  · obtain ⟨rfl, h2⟩ := List.append_inj' heq rfl
    simp only [List.cons.injEq, and_true] at h2
    subst h2; exact hd
  · exact h u e hp

/-- The pulse counters are monotone along histories. -/
lemma sent_mono (i : ℕ) (w : List Bool) (d p : Bool) :
    (run A i w).2 p ≤ (run A i (w ++ [d])).2 p := by
  rw [run_append]; simp

variable {n : ℕ} [NeZero n]

/-- The configuration in which node `v` has ID `id v` and history `f v`. -/
def syncCfg (id : ZMod n → ℕ) (f : ZMod n → List Bool) : Config (ZMod n) A.State where
  st v := (run A (id v) (f v)).1
  sent p := (run A (id p.1) (f p.1)).2 p.2
  recvd p := (f p.1).count p.2

omit [NeZero n] in
/-- With empty histories, the synchronised configuration is the initial configuration. -/
lemma syncCfg_nil (id : ZMod n → ℕ) : syncCfg (A := A) id (fun _ => []) = initCfg A id := by
  ext <;> simp [syncCfg, initCfg]

omit [NeZero n] in
/-- Delivering a pulse to a node of a synchronised configuration extends its history. -/
lemma deliver_syncCfg (id : ZMod n → ℕ) (f : ZMod n → List Bool) (v : ZMod n) (d : Bool) :
    deliver A (syncCfg id f) v d = syncCfg id (Function.update f v (f v ++ [d])) := by
  ext x
  · by_cases hx : x = v
    · subst hx; simp [deliver, syncCfg, run_append]
    · simp [deliver, syncCfg, hx]
  · obtain ⟨u, p⟩ := x
    by_cases hu : u = v
    · subst hu; simp [deliver, syncCfg, run_append]
    · simp [deliver, syncCfg, hu]
  · obtain ⟨u, p⟩ := x
    by_cases hu : u = v
    · subst hu
      simp only [deliver, syncCfg, Function.update_self, List.count_append, Prod.mk.injEq, true_and]
      cases p <;> cases d <;> simp
    · simp [deliver, syncCfg, hu]

omit [NeZero n] in
/-- On the oriented ring, a link joins ports of opposite numbers. -/
lemma oriented_peer_port (v : ZMod n) (d : Bool) : ((oriented n).peer (v, d)).2 = !d := by
  cases d <;> rfl

/-- **Lockstep lemma.** If `w` is a valid solitude history for every node's ID, the configuration
in which every node of the oriented ring has history `w` is reachable. -/
theorem reach_sync (id : ZMod n → ℕ) (w : List Bool) (hw : ∀ v, Valid A (id v) w) :
    Reach (oriented n) A id (syncCfg id fun _ => w) := by
  induction w using List.reverseRecOn with
  | nil => rw [syncCfg_nil]; exact Relation.ReflTransGen.refl
  | append_singleton w d ih =>
    have hw' : ∀ v, Valid A (id v) w := fun v => (hw v).of_prefix (List.prefix_append _ _)
    have hok : ∀ v, Ok A (id v) w d := fun v => hw v w d List.prefix_rfl
    have key : ∀ T : Finset (ZMod n),
        Reach (oriented n) A id (syncCfg id fun v => if v ∈ T then w ++ [d] else w) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simpa using ih hw'
      | insert a T ha ihT =>
        have hen :
            Enabled (oriented n) A (syncCfg id fun v => if v ∈ T then w ++ [d] else w) a d := by
          obtain ⟨h1, h2, h3⟩ := hok a
          refine ⟨by simpa [syncCfg, ha] using h1, by simpa [syncCfg, ha] using h2, ?_⟩
          set u := ((oriented n).peer (a, d)).1
          have hp : (oriented n).peer (a, d) = (u, !d) := by
            rw [← oriented_peer_port a d]
          rw [hp]
          simp only [syncCfg, ha, ite_false]
          have h3' := (hok u).2.2
          split_ifs
          · exact lt_of_lt_of_le h3' (sent_mono _ _ _ _)
          · exact h3'
        have := ihT.tail (Step.mk _ a d hen)
        rw [deliver_syncCfg] at this
        have hf : (Function.update (fun v => if v ∈ T then w ++ [d] else w) a
            ((if a ∈ T then w ++ [d] else w) ++ [d])) =
            fun v => if v ∈ insert a T then w ++ [d] else w := by
          funext v
          by_cases hv : v = a
          · subst hv; simp [ha]
          · simp [hv, Finset.mem_insert]
        rw [hf] at this; exact this
    simpa using key Finset.univ

/-- Solitude: on the 1-node ring every reachable configuration is `syncCfg` of a valid history. -/
theorem reach_one {i : ℕ} {c : Config (ZMod 1) A.State} (h : Reach (oriented 1) A (fun _ => i) c) :
    ∃ w, Valid A i w ∧ c = syncCfg (fun _ => i) fun _ => w := by
  induction h with
  | refl => exact ⟨[], Valid.nil i, (syncCfg_nil _).symm⟩
  | tail _ hs ih =>
    obtain ⟨w, hw, rfl⟩ := ih
    obtain ⟨v, d, h1, h2, h3⟩ := hs
    have hok : Ok A i w d := by
      refine ⟨by simpa [syncCfg] using h1, by simpa [syncCfg] using h2, ?_⟩
      have : (oriented 1).peer (v, d) = (v, !d) := by
        rw [Prod.ext_iff]; exact ⟨Subsingleton.elim _ _, oriented_peer_port v d⟩
      rw [this] at h3; simpa [syncCfg] using h3
    refine ⟨w ++ [d], hw.append hok, ?_⟩
    rw [deliver_syncCfg]
    congr 1
    funext x
    rw [Subsingleton.elim x v]; simp

end Cslib.ContentOblivious
