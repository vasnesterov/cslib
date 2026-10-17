/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.ContentOblivious.Staged

/-!
# Embeddings of procedures and sums of procedures

A *homomorphism* `F : P.Hom Q` of procedures maps states of `P` to states of `Q`, inputs and
results along, and commutes with start-up, reception, readiness and results. Then the executions
of `Q` from mapped inputs are exactly the images of the executions of `P`
(`Proc.Hom.reach_iff`), so composability, results and pulse bounds transfer.

The main use is `Proc.sum P Q`: a node runs `P` or `Q` depending on its input. A staged program
whose stages are of several kinds (e.g. ComputeOR and bit-sending rounds) uses a sum of procedures
as its stage procedure.
-/

@[expose] public section

namespace Cslib.ContentOblivious

open Finset

namespace Proc

variable {I R I' R' : Type*}

/-- A homomorphism (embedding) of procedures. -/
structure Hom (P : Proc I R) (Q : Proc I' R') where
  /-- The map on states. -/
  f : P.State → Q.State
  /-- The map on inputs. -/
  g : I → I'
  /-- The map on results. -/
  h : R → R'
  /-- Start-up commutes with the maps. -/
  init : ∀ a, Q.init (g a) = (f (P.init a).1, (P.init a).2)
  /-- Reception commutes with the maps. -/
  recv : ∀ s q, Q.recv (f s) q = (f (P.recv s q).1, (P.recv s q).2)
  /-- Readiness is preserved. -/
  ready : ∀ s q, Q.ready (f s) q = P.ready s q
  /-- Results commute with the maps. -/
  result : ∀ s, Q.result (f s) = (P.result s).map h

variable {P : Proc I R} {Q : Proc I' R'} (F : P.Hom Q)

/-- A homomorphism preserves termination. -/
lemma Hom.terminated (s : P.State) : Q.terminated (F.f s) = P.terminated s := by
  rw [Q.terminated_eq, P.terminated_eq, F.result]; cases P.result s <;> rfl

/-- Image of a configuration. -/
def Hom.cfg {V : Type*} (c : Config V P.State) : Config V Q.State :=
  { st := fun v => F.f (c.st v), sent := c.sent, recvd := c.recvd }

variable [Encodable I] [Inhabited I] [Encodable I'] [Inhabited I'] {V : Type*} [DecidableEq V]
  {W : Wiring V}

/-- Delivering a pulse commutes with mapping configurations. -/
lemma Hom.deliver_cfg (c : Config V P.State) (v : V) (q : Bool) :
    Cslib.ContentOblivious.deliver Q.toAlgo (F.cfg c) v q =
      F.cfg (Cslib.ContentOblivious.deliver P.toAlgo c v q) := by
  ext w
  · by_cases hw : w = v
    · subst hw; simp [Hom.cfg, Cslib.ContentOblivious.deliver, F.recv]
    · simp [Hom.cfg, Cslib.ContentOblivious.deliver, hw]
  · simp [Hom.cfg, Cslib.ContentOblivious.deliver, F.recv]
  · simp [Hom.cfg, Cslib.ContentOblivious.deliver]

omit [DecidableEq V] in
/-- Enabledness is preserved and reflected by mapping configurations. -/
lemma Hom.enabled_iff (c : Config V P.State) (v : V) (q : Bool) :
    Enabled W Q.toAlgo (F.cfg c) v q ↔ Enabled W P.toAlgo c v q := by
  simp [Enabled, Hom.cfg, F.terminated, F.ready]

omit [Encodable I] [Inhabited I] [Encodable I'] [Inhabited I'] [DecidableEq V] in
/-- The initial configuration of mapped inputs is the image of the initial configuration. -/
lemma Hom.initCfg (x : V → I) : Q.initCfg (fun v => F.g (x v)) = F.cfg (P.initCfg x) := by
  ext <;> simp [Prog.initCfg, Hom.cfg, F.init]

/-- Executions of `Q` from mapped inputs are the images of executions of `P`. -/
theorem Hom.reach_iff (x : V → I) (c : Config V Q.State) :
    Q.Reach W (fun v => F.g (x v)) c ↔ ∃ c₀, P.Reach W x c₀ ∧ c = F.cfg c₀ := by
  constructor
  · intro hc
    refine Prog.Reach.induction ⟨P.initCfg x, Prog.Reach.init x, F.initCfg x⟩ ?_ hc
    rintro c c' - ⟨v, q, hen⟩ ⟨c₀, hr, rfl⟩
    rw [F.enabled_iff] at hen
    exact ⟨_, hr.tail (Step.mk _ v q hen), F.deliver_cfg c₀ v q⟩
  · rintro ⟨c₀, hr, rfl⟩
    refine Prog.Reach.induction ?_ ?_ hr
    · rw [← F.initCfg]; exact Prog.Reach.init _
    · rintro c c' - ⟨v, q, hen⟩ ih
      rw [← F.deliver_cfg]
      exact ih.tail (Step.mk _ v q ((F.enabled_iff c v q).2 hen))

omit [DecidableEq V] in
/-- Finality is preserved and reflected by mapping configurations. -/
lemma Hom.final_iff (c : Config V P.State) : Q.Final W (F.cfg c) ↔ P.Final W c := by
  simp only [Prog.Final, Cslib.ContentOblivious.Final, F.enabled_iff]

variable [Fintype V]

/-- Pulse bounds transfer along a homomorphism. -/
theorem Hom.totalSent_le {x : V → I} {B : ℕ} (hB : ∀ c, P.Reach W x c → totalSent c ≤ B) :
    ∀ c, Q.Reach W (fun v => F.g (x v)) c → totalSent c ≤ B := by
  intro c hc
  obtain ⟨c₀, hr, rfl⟩ := (F.reach_iff x c).1 hc
  exact hB c₀ hr

/-- Composability transfers along a homomorphism. -/
theorem Hom.composable {x : V → I} (hP : P.Composable W x) :
    Q.Composable W (fun v => F.g (x v)) where
  bounded := by
    obtain ⟨B, hB⟩ := hP.bounded
    exact ⟨B, F.totalSent_le hB⟩
  final c hc hfin := by
    obtain ⟨c₀, hr, rfl⟩ := (F.reach_iff x c).1 hc
    obtain ⟨hq, hall⟩ := hP.final c₀ hr ((F.final_iff c₀).1 hfin)
    refine ⟨hq, fun v => ?_⟩
    simp only [Hom.cfg, F.result]
    have := hall v
    revert this; cases P.result (c₀.st v) <;> simp
  clean c hc v q hv hready hu := by
    obtain ⟨c₀, hr, rfl⟩ := (F.reach_iff x c).1 hc
    simp only [Hom.cfg, F.result, F.ready] at hv hready hu ⊢
    refine hP.clean c₀ hr v q ?_ hready ?_
    · revert hv; cases P.result (c₀.st v) <;> simp
    · revert hu; cases P.result (c₀.st (W.peer (v, q)).1) <;> simp

omit [Fintype V] in
/-- Results transfer along a homomorphism. -/
theorem Hom.returns {x : V → I} {r : V → R} (hP : P.Returns W x r) :
    Q.Returns W (fun v => F.g (x v)) (fun v => F.h (r v)) := by
  intro c hc hfin v
  obtain ⟨c₀, hr, rfl⟩ := (F.reach_iff x c).1 hc
  simp [Hom.cfg, F.result, hP c₀ hr ((F.final_iff c₀).1 hfin) v]

/-! ## Sums of procedures -/

variable {I₁ R₁ I₂ R₂ : Type*}

/-- The sum of two procedures: a node with input `inl a` runs `P` on `a`, a node with input
`inr b` runs `Q` on `b`. -/
def sum (P : Proc I₁ R₁) (Q : Proc I₂ R₂) : Proc (I₁ ⊕ I₂) (R₁ ⊕ R₂) where
  State := P.State ⊕ Q.State
  init
    | .inl a => (.inl (P.init a).1, (P.init a).2)
    | .inr b => (.inr (Q.init b).1, (Q.init b).2)
  recv
    | .inl s, q => (.inl (P.recv s q).1, (P.recv s q).2)
    | .inr t, q => (.inr (Q.recv t q).1, (Q.recv t q).2)
  ready
    | .inl s, q => P.ready s q
    | .inr t, q => Q.ready t q
  terminated
    | .inl s => P.terminated s
    | .inr t => Q.terminated t
  result
    | .inl s => (P.result s).map .inl
    | .inr t => (Q.result t).map .inr
  terminated_eq
    | .inl s => by
      change P.terminated s = ((P.result s).map Sum.inl).isSome
      rw [P.terminated_eq]; cases P.result s <;> rfl
    | .inr t => by
      change Q.terminated t = ((Q.result t).map Sum.inr).isSome
      rw [Q.terminated_eq]; cases Q.result t <;> rfl

/-- The left summand embeds in the sum. -/
def Hom.inl (P : Proc I₁ R₁) (Q : Proc I₂ R₂) : P.Hom (P.sum Q) where
  f := .inl
  g := .inl
  h := .inl
  init _ := rfl
  recv _ _ := rfl
  ready _ _ := rfl
  result _ := rfl

/-- The right summand embeds in the sum. -/
def Hom.inr (P : Proc I₁ R₁) (Q : Proc I₂ R₂) : Q.Hom (P.sum Q) where
  f := .inr
  g := .inr
  h := .inr
  init _ := rfl
  recv _ _ := rfl
  ready _ _ := rfl
  result _ := rfl

end Proc

end Cslib.ContentOblivious
