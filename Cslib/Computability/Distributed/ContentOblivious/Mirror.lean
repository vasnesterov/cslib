/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.ContentOblivious.Compose
public import Mathlib.Tactic.Ring
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Equiv.Bool

/-!
# Mirror images of procedures on oriented rings, and generic invariant tools

## Mirror images

The *mirror image* `P.mirror` of a program `P` is `P` with its two ports swapped: it sends on
`Port0` whatever `P` sends on `Port1` and vice versa, and reads from `Port0` when `P` reads from
`Port1`. On the oriented ring, the reflection `v ↦ -v` of `ZMod n` maps clockwise links to
counter-clockwise links, so running `P.mirror` with inputs `x` is the same as running `P` with
inputs `x ∘ (fun v => -v)`, up to the map `Config.mirror` of configurations (reflect the nodes,
swap the ports). Hence reachability, final configurations, quiescence, message complexity,
composability and results transfer (`Prog.reach_mirror_iff`, `Proc.composable_mirror_iff`,
`Proc.returns_mirror_iff`, …). This formalizes the usual "symmetric, omitted" argument (e.g.
CWBitSending vs. CCWBitSending in Chalopin, Chang, Di Luna, Zhou, PODC 2026).

## Generic invariant tools

* `Prog.Reach.local_inv`: a *local* invariant relating the state of a node to its own ghost
  counters (pulses received and sent per port) holds in every reachable configuration as soon as
  it holds initially and is preserved by every reception the node is willing to make.
* `Ring.chain_ccw`, `Ring.chain_cw`: propagation of a property along an oriented ring
  `ZMod n`, step by step, except across one excluded link.
-/

@[expose] public section

namespace Cslib.ContentOblivious

open Finset

variable {I R : Type*}

/-! ## Mirror images -/

/-- The mirror image of a program: the two ports are swapped. -/
def Prog.mirror (P : Prog I) : Prog I where
  State := P.State
  init a := ((P.init a).1, fun p => (P.init a).2 (!p))
  recv s j := ((P.recv s (!j)).1, fun p => (P.recv s (!j)).2 (!p))
  ready s j := P.ready s (!j)
  terminated := P.terminated

/-- The mirror image of a procedure: the two ports are swapped. -/
def Proc.mirror (P : Proc I R) : Proc I R :=
  { P.toProg.mirror with
    result := P.result
    terminated_eq := P.terminated_eq }

/-- Reflection of a configuration of a ring `ZMod n`: node `v` becomes node `-v` and the two
ports are swapped. -/
def Config.mirror {n : ℕ} {S : Type*} (c : Config (ZMod n) S) : Config (ZMod n) S where
  st v := c.st (-v)
  sent p := c.sent (-p.1, !p.2)
  recvd p := c.recvd (-p.1, !p.2)

namespace Config

variable {n : ℕ} {S : Type*}

/-- The local states of the mirror configuration. -/
@[simp] lemma mirror_st (c : Config (ZMod n) S) (v : ZMod n) : c.mirror.st v = c.st (-v) := rfl
/-- The sent counters of the mirror configuration. -/
@[simp] lemma mirror_sent (c : Config (ZMod n) S) (p : ZMod n × Bool) :
    c.mirror.sent p = c.sent (-p.1, !p.2) := rfl
/-- The received counters of the mirror configuration. -/
@[simp] lemma mirror_recvd (c : Config (ZMod n) S) (p : ZMod n × Bool) :
    c.mirror.recvd p = c.recvd (-p.1, !p.2) := rfl

/-- Mirroring is an involution. -/
@[simp] lemma mirror_mirror (c : Config (ZMod n) S) : c.mirror.mirror = c := by
  ext <;> simp

/-- Mirroring is injective. -/
lemma mirror_injective : Function.Injective (Config.mirror (n := n) (S := S)) := by
  intro c d h
  rw [← mirror_mirror c, h, mirror_mirror]

end Config

/-- The reflection `v ↦ -v` with swapped ports is an automorphism of the oriented ring. -/
lemma oriented_peer_mirror (n : ℕ) (v : ZMod n) (j : Bool) :
    (oriented n).peer (-v, !j) =
      (-((oriented n).peer (v, j)).1, !((oriented n).peer (v, j)).2) := by
  cases j <;> simp [oriented] <;> ring

namespace Prog

variable (P : Prog I) {n : ℕ}

/-- The mirror image reads from the swapped port. -/
@[simp] lemma mirror_ready (s : P.State) (j : Bool) : P.mirror.ready s j = P.ready s (!j) := rfl
/-- Mirroring does not change termination. -/
@[simp] lemma mirror_terminated (s : P.State) : P.mirror.terminated s = P.terminated s := rfl
/-- The mirror image sends on the swapped ports. -/
@[simp] lemma mirror_recv (s : P.State) (j : Bool) :
    P.mirror.recv s j = ((P.recv s (!j)).1, fun p => (P.recv s (!j)).2 (!p)) := rfl
/-- The mirror image starts with the swapped sends. -/
@[simp] lemma mirror_init (a : I) :
    P.mirror.init a = ((P.init a).1, fun p => (P.init a).2 (!p)) := rfl

variable [Encodable I] [Inhabited I]

/-- Enabledness for the mirror image is enabledness for the original on the mirror configuration. -/
lemma mirror_enabled (c : Config (ZMod n) P.State) (v : ZMod n) (j : Bool) :
    Enabled (oriented n) P.mirror.toAlgo c v j ↔
      Enabled (oriented n) P.toAlgo c.mirror (-v) (!j) := by
  unfold Enabled
  have h := oriented_peer_mirror n v j
  simp only [mirror_terminated, mirror_ready, Config.mirror_st,
    neg_neg, Config.mirror_recvd, Config.mirror_sent, Bool.not_not, h]

/-- Delivery for the mirror image is delivery for the original on the mirror configuration. -/
lemma mirror_deliver (c : Config (ZMod n) P.State) (v : ZMod n) (j : Bool) :
    (deliver P.mirror.toAlgo c v j).mirror = deliver P.toAlgo c.mirror (-v) (!j) := by
  ext w
  · simp only [Config.mirror_st, deliver, Function.update_apply]
    by_cases h : w = -v
    · subst h; simp; rfl
    · have h' : -w ≠ v := fun h' => h (by rw [← h', neg_neg])
      simp [h, h']
  · rcases w with ⟨w, p⟩
    simp only [Config.mirror_sent, deliver]
    by_cases h : w = -v
    · subst h; simp
    · have h' : -w ≠ v := fun h' => h (by rw [← h', neg_neg])
      simp [h, h']
  · rcases w with ⟨w, p⟩
    simp only [Config.mirror_recvd, deliver]
    by_cases h : w = -v
    · subst h; cases p <;> cases j <;> simp
    · have h' : -w ≠ v := fun h' => h (by rw [← h', neg_neg])
      simp [h, h']

/-- Steps of the original map to steps of the mirror image on mirror configurations. -/
lemma mirror_step {c e : Config (ZMod n) P.State}
    (h : ContentOblivious.Step (oriented n) P.toAlgo c e) :
    ContentOblivious.Step (oriented n) P.mirror.toAlgo c.mirror e.mirror := by
  obtain ⟨v, j, hen⟩ := h
  have hd := mirror_deliver P c.mirror (-v) (!j)
  simp only [Config.mirror_mirror, neg_neg, Bool.not_not] at hd
  have hd' : (deliver P.toAlgo c v j).mirror = deliver P.mirror.toAlgo c.mirror (-v) (!j) := by
    exact (congrArg Config.mirror hd.symm).trans (Config.mirror_mirror _)
  rw [hd']
  refine ContentOblivious.Step.mk _ _ _ ((mirror_enabled P _ _ _).2 ?_)
  simpa using hen

/-- Steps of the mirror image are the mirrors of steps of the original. -/
lemma mirror_step_iff (c d : Config (ZMod n) P.State) :
    ContentOblivious.Step (oriented n) P.mirror.toAlgo c d ↔
      ContentOblivious.Step (oriented n) P.toAlgo c.mirror d.mirror := by
  constructor
  · rintro ⟨v, j, hen⟩
    have hd := mirror_deliver P c v j
    have hs := ContentOblivious.Step.mk _ _ _ ((mirror_enabled P c v j).1 hen)
    exact cast
      (congrArg (fun e => ContentOblivious.Step (oriented n) P.toAlgo c.mirror e) hd.symm) hs
  · intro h
    simpa using mirror_step P h

/-- The mirror of the initial configuration of the mirror image is the initial configuration of the
original with reflected inputs. -/
lemma mirror_initCfg (x : ZMod n → I) :
    (Cslib.ContentOblivious.initCfg P.mirror.toAlgo fun v => Encodable.encode (x v)).mirror =
      Cslib.ContentOblivious.initCfg P.toAlgo fun v => Encodable.encode ((x ∘ Neg.neg) v) := by
  ext <;> simp [Cslib.ContentOblivious.initCfg]
  all_goals rfl

/-- Executions of `P.mirror` with inputs `x` are the reflections of executions of `P` with inputs
`x ∘ (fun v => -v)`. -/
theorem reach_mirror_iff (x : ZMod n → I) (c : Config (ZMod n) P.State) :
    P.mirror.Reach (oriented n) x c ↔ P.Reach (oriented n) (x ∘ Neg.neg) c.mirror := by
  constructor
  · intro h
    unfold Reach at h ⊢
    induction h with
    | refl =>
      have := mirror_initCfg P x
      exact this ▸ Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.tail ((mirror_step_iff P _ _).1 hs)
  · suffices ∀ d, P.Reach (oriented n) (x ∘ Neg.neg) d → P.mirror.Reach (oriented n) x d.mirror by
      intro h; simpa using this _ h
    intro d h
    unfold Reach at h ⊢
    induction h with
    | refl =>
      have h0 : (Cslib.ContentOblivious.initCfg P.toAlgo
          fun v => Encodable.encode ((x ∘ Neg.neg) v)).mirror =
          Cslib.ContentOblivious.initCfg P.mirror.toAlgo fun v => Encodable.encode (x v) := by
        rw [← mirror_initCfg P x]; exact Config.mirror_mirror _
      exact (congrArg (fun e => Relation.ReflTransGen _ _ e) h0).mpr Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.tail (mirror_step P hs)

/-- Final configurations of the mirror image are the mirrors of final configurations. -/
lemma final_mirror_iff (c : Config (ZMod n) P.State) :
    P.mirror.Final (oriented n) c ↔ P.Final (oriented n) c.mirror := by
  constructor
  · intro h v j hen
    exact h (-v) (!j) ((mirror_enabled P c (-v) (!j)).2 (by simpa using hen))
  · intro h v j hen
    exact h _ _ ((mirror_enabled P c v j).1 hen)

/-- Quiescent configurations of the mirror image are the mirrors of quiescent configurations. -/
lemma quiescent_mirror_iff (c : Config (ZMod n) P.State) :
    P.mirror.Quiescent (oriented n) c ↔ P.Quiescent (oriented n) c.mirror := by
  constructor
  · rintro h ⟨v, j⟩
    have := h (-v, !j)
    simp only [Config.mirror_recvd, Config.mirror_sent, oriented_peer_mirror] at this ⊢
    simpa using this
  · rintro h ⟨v, j⟩
    have := h (-v, !j)
    simp only [Config.mirror_recvd, Config.mirror_sent, oriented_peer_mirror, neg_neg,
      Bool.not_not] at this ⊢
    simpa using this

end Prog

/-- Mirroring does not change the number of pulses sent. -/
lemma totalSent_mirror {n : ℕ} [NeZero n] {S : Type*} (c : Config (ZMod n) S) :
    totalSent c.mirror = totalSent c := by
  unfold totalSent
  exact Fintype.sum_equiv ((Equiv.neg (ZMod n)).prodCongr Equiv.boolNot) _ _ (fun p => rfl)

namespace Proc

variable (P : Proc I R) {n : ℕ}

/-- Mirroring does not change results. -/
@[simp] lemma mirror_result (s : P.State) : P.mirror.result s = P.result s := rfl
/-- The underlying program of the mirror procedure is the mirror program. -/
@[simp] lemma mirror_toProg : P.mirror.toProg = P.toProg.mirror := rfl

variable [Encodable I] [Inhabited I]

/-- Reachability for the mirror procedure is reachability for the original with reflected inputs. -/
lemma reach_mirror_iff (x : ZMod n → I) (c : Config (ZMod n) P.State) :
    P.mirror.Reach (oriented n) x c ↔ P.Reach (oriented n) (x ∘ Neg.neg) c.mirror :=
  Prog.reach_mirror_iff P.toProg x c

/-- Reachability for the original with reflected inputs is reachability for the mirror procedure. -/
lemma reach_mirror_iff' (x : ZMod n → I) (c : Config (ZMod n) P.State) :
    P.Reach (oriented n) (x ∘ Neg.neg) c ↔ P.mirror.Reach (oriented n) x c.mirror := by
  rw [reach_mirror_iff, Config.mirror_mirror]

/-- Final configurations of the mirror procedure are the mirrors of final configurations. -/
lemma final_mirror_iff (c : Config (ZMod n) P.State) :
    P.mirror.Final (oriented n) c ↔ P.Final (oriented n) c.mirror :=
  Prog.final_mirror_iff P.toProg c

/-- Quiescent configurations of the mirror procedure are the mirrors of quiescent configurations. -/
lemma quiescent_mirror_iff (c : Config (ZMod n) P.State) :
    P.mirror.Quiescent (oriented n) c ↔ P.Quiescent (oriented n) c.mirror :=
  Prog.quiescent_mirror_iff P.toProg c

/-- Transfer of results to the mirror image. -/
theorem returns_mirror_iff (x : ZMod n → I) (r : ZMod n → R) :
    P.mirror.Returns (oriented n) x r ↔ P.Returns (oriented n) (x ∘ Neg.neg) (r ∘ Neg.neg) := by
  constructor
  · intro h c hc hf v
    have hf' : P.mirror.Final (oriented n) c.mirror := by
      rw [final_mirror_iff, Config.mirror_mirror]; exact hf
    simpa [Config.mirror, Proc.mirror, Prog.mirror] using
      h _ ((reach_mirror_iff' P x c).1 hc) hf' (-v)
  · intro h c hc hf v
    simpa [Config.mirror, Proc.mirror, Prog.mirror] using
      h _ ((reach_mirror_iff P x c).1 hc) ((final_mirror_iff P c).1 hf) (-v)

variable [NeZero n]

/-- Transfer of composability to the mirror image. -/
theorem composable_mirror_iff (x : ZMod n → I) :
    P.mirror.Composable (oriented n) x ↔ P.Composable (oriented n) (x ∘ Neg.neg) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨B, hB⟩ := h.bounded
      refine ⟨B, fun c hc => ?_⟩
      rw [← totalSent_mirror]
      exact hB _ ((reach_mirror_iff' P x c).1 hc)
    · intro c hc hf
      have hc' := (reach_mirror_iff' P x c).1 hc
      have hf' : P.mirror.Final (oriented n) c.mirror := by
        rw [final_mirror_iff, Config.mirror_mirror]; exact hf
      obtain ⟨hq, hr⟩ := h.final _ hc' hf'
      refine ⟨?_, fun v => by simpa [Config.mirror, Proc.mirror, Prog.mirror] using hr (-v)⟩
      rw [quiescent_mirror_iff, Config.mirror_mirror] at hq
      exact hq
    · intro c hc v j hv hrd hpeer
      have := h.clean _ ((reach_mirror_iff' P x c).1 hc) (-v) (!j)
        (by simpa [Config.mirror, Proc.mirror, Prog.mirror] using hv)
        (by simpa [Config.mirror, Proc.mirror, Prog.mirror] using hrd)
        (by simpa [Config.mirror, Proc.mirror, Prog.mirror, oriented_peer_mirror] using hpeer)
      simpa [Config.mirror, Proc.mirror, Prog.mirror, oriented_peer_mirror] using this
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨B, hB⟩ := h.bounded
      refine ⟨B, fun c hc => ?_⟩
      rw [← totalSent_mirror]
      exact hB _ ((reach_mirror_iff P x c).1 hc)
    · intro c hc hf
      have hc' := (reach_mirror_iff P x c).1 hc
      have hf' : P.Final (oriented n) c.mirror := (final_mirror_iff P c).1 hf
      obtain ⟨hq, hr⟩ := h.final _ hc' hf'
      refine ⟨(quiescent_mirror_iff P c).2 hq,
        fun v => by simpa [Config.mirror, Proc.mirror, Prog.mirror] using hr (-v)⟩
    · intro c hc v j hv hrd hpeer
      have := h.clean _ ((reach_mirror_iff P x c).1 hc) (-v) (!j)
        (by simpa [Config.mirror, Proc.mirror, Prog.mirror] using hv)
        (by simpa [Config.mirror, Proc.mirror, Prog.mirror] using hrd)
        (by simpa [Config.mirror, Proc.mirror, Prog.mirror, oriented_peer_mirror] using hpeer)
      simpa [Config.mirror, Proc.mirror, Prog.mirror, oriented_peer_mirror] using this

/-- Transfer of pulse bounds to the mirror image. -/
theorem totalSent_mirror_le_iff (x : ZMod n → I) (B : ℕ) :
    (∀ c, P.mirror.Reach (oriented n) x c → totalSent c ≤ B) ↔
      ∀ c, P.Reach (oriented n) (x ∘ Neg.neg) c → totalSent c ≤ B := by
  constructor
  · intro h c hc
    rw [← totalSent_mirror]; exact h _ ((reach_mirror_iff' P x c).1 hc)
  · intro h c hc
    rw [← totalSent_mirror]; exact h _ ((reach_mirror_iff P x c).1 hc)

end Proc


/-! ## Local invariants -/

namespace Prog

variable [Encodable I] [Inhabited I] {P : Prog I} {V : Type*} [DecidableEq V] {W : Wiring V}

/-- A *local invariant* `Rel a s r snt` relating the input `a`, the state `s` and the ghost
counters of a node (`r p`: pulses received on port `p`, `snt p`: pulses sent on port `p`) holds
for every node of every reachable configuration, as soon as it holds after start-up and is
preserved by every reception that the node is willing to make. -/
theorem Reach.local_inv (Rel : I → P.State → (Bool → ℕ) → (Bool → ℕ) → Prop)
    (hinit : ∀ a, Rel a (P.init a).1 (fun _ => 0) (P.init a).2)
    (hstep : ∀ a s (r snt : Bool → ℕ) j, Rel a s r snt → P.terminated s = false →
      P.ready s j = true →
      Rel a (P.recv s j).1 (fun p => r p + if p = j then 1 else 0)
        (fun p => snt p + (P.recv s j).2 p))
    {x : V → I} {c : Config V P.State} (hc : P.Reach W x c) (v : V) :
    Rel (x v) (c.st v) (fun p => c.recvd (v, p)) (fun p => c.sent (v, p)) := by
  refine Reach.induction (motive := fun c => ∀ v, Rel (x v) (c.st v) (fun p => c.recvd (v, p))
    (fun p => c.sent (v, p))) (fun v => hinit (x v)) ?_ hc v
  intro c c' _ hs ih v
  · obtain ⟨w, j, hen⟩ := hs
    by_cases hv : v = w
    · subst hv
      have := hstep _ _ _ _ j (ih v) hen.1 hen.2.1
      convert this using 2
      · simp [deliver]
      · simp [deliver, Prod.ext_iff]
      · simp [deliver]
    · have e1 : (deliver P.toAlgo c w j).st v = c.st v := by simp [deliver, hv]
      have e2 : (fun p => (deliver P.toAlgo c w j).recvd (v, p)) = fun p => c.recvd (v, p) := by
        funext p; simp [deliver, hv]
      have e3 : (fun p => (deliver P.toAlgo c w j).sent (v, p)) = fun p => c.sent (v, p) := by
        funext p; simp [deliver, hv]
      rw [e1, e2, e3]; exact ih v

end Prog

/-! ## Propagation along an oriented ring -/

namespace Ring

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- A positive natural number below `n` is nonzero in `ZMod n`. -/
lemma natCast_ne_zero {k : ℕ} (h0 : 0 < k) (hk : k < n) : (k : ZMod n) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd h0 h) (not_le.2 hk)

omit [NeZero n] in
/-- Counter-clockwise propagation: if `S` passes from `v + 1` to `v` for every `v ≠ m`, then it
passes from `m + 1 + k` down to `m + 1`, through every `m + 1 + j`, `j ≤ k`. -/
theorem chain_ccw (S : ZMod n → Prop) (m : ZMod n) (h : ∀ v, v ≠ m → S (v + 1) → S v)
    {k : ℕ} (hk : k < n) (hS : S (m + 1 + k)) : ∀ j ≤ k, S (m + 1 + j) := by
  suffices ∀ i ≤ k, S (m + 1 + ((k - i : ℕ) : ZMod n)) by
    intro j hj
    have := this (k - j) (Nat.sub_le _ _)
    rwa [Nat.sub_sub_self hj] at this
  intro i
  induction i with
  | zero => intro _; simpa using hS
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    apply h
    · intro he
      have : ((1 + (k - (i + 1)) : ℕ) : ZMod n) = 0 := by
        push_cast
        have := congrArg (· - m) he
        simp only [sub_self] at this
        rw [← this]; ring
      exact natCast_ne_zero (by omega) (by omega) this
    · have e : m + 1 + ((k - (i + 1) : ℕ) : ZMod n) + 1 = m + 1 + ((k - i : ℕ) : ZMod n) := by
        rw [show k - i = (k - (i + 1)) + 1 by omega]; push_cast; ring
      rwa [e]

/-- Counter-clockwise propagation all around the ring, starting from the excluded node. -/
theorem chain_ccw_all (S : ZMod n → Prop) (m : ZMod n) (h : ∀ v, v ≠ m → S (v + 1) → S v)
    (hS : S m) (v : ZMod n) : S v := by
  have hn : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne n)) one_pos
  have e : m + 1 + ((n - 1 : ℕ) : ZMod n) = m := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (NeZero.ne n))]; simp
  have := chain_ccw S m h hn (by rw [e]; exact hS) (v - m - 1).val
    (by have := ZMod.val_lt (v - m - 1); omega)
  simpa [ZMod.natCast_zmod_val] using this

/-- Counter-clockwise propagation from any node down to `m + 1`. -/
theorem chain_ccw_to (S : ZMod n → Prop) (m : ZMod n) (h : ∀ v, v ≠ m → S (v + 1) → S v)
    (w : ZMod n) (hS : S w) : S (m + 1) := by
  have := chain_ccw S m h (k := (w - m - 1).val) (ZMod.val_lt _)
    (by simpa [ZMod.natCast_zmod_val] using hS) 0 (Nat.zero_le _)
  simpa using this

omit [NeZero n] in
/-- Clockwise propagation: if `S` passes from `v` to `v + 1` for every `v ≠ m`, then it passes
from `m + 1` to every `m + 1 + j`, `j < n`. -/
theorem chain_cw (S : ZMod n → Prop) (m : ZMod n) (h : ∀ v, v ≠ m → S v → S (v + 1))
    (hS : S (m + 1)) : ∀ j < n, S (m + 1 + j) := by
  intro j
  induction j with
  | zero => intro _; simpa using hS
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have := h _ (by
      intro he
      have : ((1 + j : ℕ) : ZMod n) = 0 := by
        have := congrArg (· - m) he
        simp only [sub_self] at this
        push_cast; rw [← this]; ring
      exact natCast_ne_zero (by omega) (by omega) this) h1
    rwa [show m + 1 + (j : ZMod n) + 1 = m + 1 + ((j + 1 : ℕ) : ZMod n) by push_cast; ring] at this

/-- Clockwise propagation all around the ring. -/
theorem chain_cw_all (S : ZMod n → Prop) (m : ZMod n) (h : ∀ v, v ≠ m → S v → S (v + 1))
    (hS : S (m + 1)) (v : ZMod n) : S v := by
  have := chain_cw S m h hS (v - m - 1).val (ZMod.val_lt _)
  simpa [ZMod.natCast_zmod_val] using this

end Ring

end Cslib.ContentOblivious
