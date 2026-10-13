/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.SharedMemory.Valency

/-!
# Lower bounds for binary consensus apply to multivalued consensus

An algorithm `I` for consensus on values `V` (with validity) yields an algorithm `I.toBinary v₀ v₁`
for binary consensus on the same base objects: inputs `false`/`true` are encoded as `v₀`/`v₁`, and
a decision `r` is decoded as `r = v₁`. Executions of `I.toBinary` are simulated step by step by
executions of `I`, so

* `Impl.solves_toBinary`: if `I` solves `consensus P V` then `I.toBinary` solves
  `weakConsensus P Bool`;
* `Impl.oneShotOF_toBinary`: one-shot obstruction-freedom transfers;
* allowed invocations transfer (by definition).

Hence every lower bound proved for binary consensus with weak validity (`BinCons`) holds for
`m`-valued consensus (`m ≥ 2`), e.g. for "`n`-consensus".
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace Cslib.SharedMemory

variable {ι : Type} {B : ι → ObjSpec} {P L V : Type} [DecidableEq P] [DecidableEq ι]
  [Inhabited V] [DecidableEq V]

omit [DecidableEq P] [DecidableEq ι] in
lemma Config.ext' {A : ObjSpec} {C D : Config A B P L} (h1 : C.loc = D.loc) (h2 : C.pend = D.pend)
    (h3 : C.mem = D.mem) : C = D := by
  cases C; cases D; simp_all

/-- The object specification of `V`-valued consensus: definitionally `MCons V`, spelled out as
a reducible structure (as `BinCons`). -/
abbrev MCons (V : Type) [Inhabited V] : ObjSpec where
  State := Unit
  Op := V
  Resp := V
  init := ()
  δ _ _ := ((), default)

example : MCons V = taskObj V V := rfl

namespace Impl

/-- Encoding of binary inputs. -/
def enc (v₀ v₁ : V) (b : Bool) : V := if b then v₁ else v₀

/-- Decoding of decisions. -/
def dec (v₁ : V) (r : V) : Bool := decide (r = v₁)

/-- The binary-consensus algorithm obtained from a `V`-valued consensus algorithm. -/
def toBinary (I : Impl (MCons V) B P L) (v₀ v₁ : V) : Impl BinCons B P L where
  memInit := I.memInit
  locInit := I.locInit
  invoke p l b := I.invoke p l (enc v₀ v₁ b)
  act p l := match I.act p l with
    | .access i o k => .access i o k
    | .ret r l' => .ret (dec v₁ r) l'
  allowed p b := I.allowed p (enc v₀ v₁ b)

variable (I : Impl (MCons V) B P L) (v₀ v₁ : V)

/-- Configurations of the binary algorithm as configurations of the original one. -/
def trB (C : Config BinCons B P L) : Config (MCons V) B P L :=
  ⟨C.loc, fun p => (C.pend p).map (enc v₀ v₁), C.mem⟩

/-- Labels of the two algorithms that correspond to each other. -/
def LblRel : Label P BinCons → Label P (MCons V) → Prop
  | .inv p b, ℓ' => ℓ' = .inv p (enc v₀ v₁ b)
  | .tau p, ℓ' => ℓ' = .tau p
  | .ret p b, ℓ' => ∃ r : V, ℓ' = .ret p r ∧ dec v₁ r = b

omit [DecidableEq P] [DecidableEq ι] in
lemma toBinary_act_access {p : P} {l : L} {i : ι} {o : (B i).Op} {k : (B i).Resp → L}
    (h : I.act p l = .access i o k) : (I.toBinary v₀ v₁).act p l = .access i o k := by
  simp [toBinary, h]

omit [DecidableEq P] [DecidableEq ι] in
lemma toBinary_act_ret {p : P} {l l' : L} {r : V} (h : I.act p l = .ret r l') :
    (I.toBinary v₀ v₁).act p l = .ret (dec v₁ r) l' := by
  simp [toBinary, h]

lemma toBinary_step {C C' : Config BinCons B P L} {ℓ : Label P BinCons}
    (h : (I.toBinary v₀ v₁).step C ℓ = some C') :
    ∃ ℓ', LblRel v₀ v₁ ℓ ℓ' ∧ I.step (trB v₀ v₁ C) ℓ' = some (trB v₀ v₁ C') := by
  classical
  cases ℓ with
  | inv p b =>
    obtain ⟨h0, h1, h2, h3, h4⟩ := step_inv h
    refine ⟨.inv p (enc v₀ v₁ b), rfl, ?_⟩
    have hp : (trB v₀ v₁ C).pend p = none := by simpa [trB] using h0
    obtain ⟨D, hD⟩ : ∃ D, I.step (trB v₀ v₁ C) (.inv p (enc v₀ v₁ b)) = some D :=
      Option.isSome_iff_exists.1 (by simp only [step, hp, true_and, Option.isSome_ite]; exact h1)
    obtain ⟨-, -, g2, g3, g4⟩ := step_inv hD
    rw [hD]; congr 1
    refine Config.ext' ?_ ?_ ?_
    · rw [g3]; simp only [trB, h3]; rfl
    · rw [g2]; funext q; simp only [trB, h2]
      by_cases hq : q = p
      · subst hq; simp
      · simp [hq]
    · rw [g4]; simp [trB, h4]
  | tau p =>
    obtain ⟨h0, h1, i, o, k, hact, hm, hl⟩ := step_tau h
    refine ⟨.tau p, rfl, ?_⟩
    have hact' : I.act p (C.loc p) = .access i o k := by
      simp only [toBinary] at hact
      split at hact
      · rename_i i' o' k' he; rw [he]; cases hact; rfl
      · cases hact
    have hp : (trB v₀ v₁ C).pend p ≠ none := by simpa [trB] using h0
    obtain ⟨D, hD⟩ : ∃ D, I.step (trB v₀ v₁ C) (.tau p) = some D :=
      Option.isSome_iff_exists.1 (by
        simp only [step, trB, Option.map_eq_none_iff, hact', Option.isSome_ite']; exact h0)
    obtain ⟨-, g1, i', o', k', ha, g2, g3⟩ := step_tau hD
    simp only [trB] at ha
    rw [hact'] at ha
    simp only [Action.access.injEq] at ha
    obtain ⟨rfl, ho, hk⟩ := ha
    cases ho; cases hk
    rw [hD]; congr 1
    refine Config.ext' ?_ ?_ ?_
    · rw [g3]; simp [trB, hl]
    · rw [g1]; simp [trB, h1]
    · rw [g2]; simp [trB, hm]
  | ret p b =>
    obtain ⟨h0, h1, h2, l, hact, hl⟩ := step_ret h
    simp only [toBinary] at hact
    split at hact
    · cases hact
    · rename_i r l' he
      simp only [Action.ret.injEq] at hact
      obtain ⟨hb, rfl⟩ := hact
      refine ⟨.ret p r, ⟨r, rfl, hb⟩, ?_⟩
      have hp : (trB v₀ v₁ C).pend p ≠ none := by simpa [trB] using h0
      obtain ⟨D, hD⟩ : ∃ D, I.step (trB v₀ v₁ C) (.ret p r) = some D :=
        Option.isSome_iff_exists.1 (by
          simp only [step, trB, Option.map_eq_none_iff, he, ↓reduceIte, Option.isSome_ite']
          exact h0)
      obtain ⟨-, g1, g2, l₂, ha, g3⟩ := step_ret hD
      simp only [trB] at ha
      rw [he] at ha; simp only [Action.ret.injEq] at ha
      obtain ⟨-, rfl⟩ := ha
      rw [hD]; congr 1
      refine Config.ext' ?_ ?_ ?_
      · rw [g3]; simp [trB, hl]
      · rw [g1]; funext q; simp only [trB, h1]
        by_cases hq : q = p
        · subst hq; simp
        · simp [hq]
      · rw [g2]; simp [trB, h2]

lemma toBinary_runFrom {C C' : Config BinCons B P L} {α : List (Label P BinCons)}
    (h : (I.toBinary v₀ v₁).runFrom C α = some C') :
    ∃ α', List.Forall₂ (LblRel v₀ v₁) α α' ∧ I.runFrom (trB v₀ v₁ C) α' = some (trB v₀ v₁ C') := by
  induction α generalizing C with
  | nil => simp only [runFrom_nil, Option.some.injEq] at h; subst h; exact ⟨[], .nil, rfl⟩
  | cons ℓ α ih =>
    simp only [runFrom_cons] at h
    cases hs : (I.toBinary v₀ v₁).step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨ℓ', hr, hs'⟩ := toBinary_step I v₀ v₁ hs
      obtain ⟨α', hα', hr'⟩ := ih h
      exact ⟨ℓ' :: α', .cons hr hα', by simp [hs', hr']⟩

lemma opsOf_rel {α : List (Label P BinCons)} {α' : List (Label P (MCons V))}
    (h : List.Forall₂ (LblRel v₀ v₁) α α') (q : P) :
    opsOf α' q = (opsOf α q).map (enc v₀ v₁) := by
  induction h with
  | nil => rfl
  | @cons ℓ ℓ' l l' hr _ ih =>
    cases ℓ with
    | inv p b =>
      simp only [LblRel] at hr; subst hr
      by_cases hq : p = q
      · subst hq; simp [opsOf_cons, ih]
      · simp [opsOf_cons, ih, hq]
    | tau p => simp only [LblRel] at hr; subst hr; simp [opsOf_cons, ih]
    | ret p b => obtain ⟨r, rfl, -⟩ := hr; simp [opsOf_cons, ih]

lemma respsOf_rel {α : List (Label P BinCons)} {α' : List (Label P (MCons V))}
    (h : List.Forall₂ (LblRel v₀ v₁) α α') (q : P) :
    respsOf α q = (respsOf α' q).map (dec v₁) := by
  induction h with
  | nil => rfl
  | @cons ℓ ℓ' l l' hr _ ih =>
    cases ℓ with
    | inv p b => simp only [LblRel] at hr; subst hr; simp [respsOf_cons, ih]
    | tau p => simp only [LblRel] at hr; subst hr; simp [respsOf_cons, ih]
    | ret p b =>
      obtain ⟨r, rfl, hb⟩ := hr
      by_cases hq : p = q
      · subst hq; simp [respsOf_cons, ih, hb]
      · simp [respsOf_cons, ih, hq]

lemma oneShot_rel {α : List (Label P BinCons)} {α' : List (Label P (MCons V))}
    (h : List.Forall₂ (LblRel v₀ v₁) α α') (h1 : OneShot α) : OneShot α' := fun q => by
  have := opsOf_rel v₀ v₁ h q
  have e : (opsOf α' q).length = (opsOf α q).length := by
    rw [this, List.length_map]
  rw [e]; exact h1 q

/-- Consensus with validity on `V` gives binary consensus with weak validity. -/
theorem solves_toBinary (hne : v₀ ≠ v₁) (hS : I.Solves (consensus P V)) :
    (I.toBinary v₀ v₁).Solves (weakConsensus P Bool) := by
  have key : ∀ α : List (Label P BinCons), (I.toBinary v₀ v₁).Valid α → OneShot α →
      (∀ p q (x y : Bool), (respsOf α p).head? = some x → (respsOf α q).head? = some y → x = y) ∧
      ∀ v : Bool, (∀ q (x : Bool), (opsOf α q).head? = some x → x = v) →
        ∀ p (y : Bool), (respsOf α p).head? = some y → y = v := by
    intro α ⟨C, hC⟩ h1
    obtain ⟨α', hrel, hrun⟩ := toBinary_runFrom I v₀ v₁ hC
    have h1' := oneShot_rel v₀ v₁ hrel h1
    obtain ⟨hag, hval⟩ := hS α' ⟨_, hrun⟩ h1'
    have hout : ∀ p (y : Bool), (respsOf α p).head? = some y →
        ∃ r : V, (respsOf α' p).head? = some r ∧ dec v₁ r = y := by
      intro p y hy
      rw [respsOf_rel v₀ v₁ hrel, List.head?_map] at hy
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hy
      exact ⟨r, hr, rfl⟩
    refine ⟨fun p q x y hx hy => ?_, fun v hv p y hy => ?_⟩
    · obtain ⟨r, hr, rfl⟩ := hout p x hx
      obtain ⟨r', hr', rfl⟩ := hout q y hy
      rw [hag p q r r' hr hr']
    · obtain ⟨r, hr, rfl⟩ := hout p y hy
      obtain ⟨q, hq⟩ := hval p r hr
      change (opsOf α' q).head? = some r at hq
      rw [opsOf_rel v₀ v₁ hrel, List.head?_map] at hq
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hq
      have := hv q b hb
      subst this
      cases b <;> simp [enc, dec, hne]
  intro α hα h1
  exact key α hα h1

lemma toBinary_soloStep (C : Config BinCons B P L) (p : P) :
    I.soloStep p (trB v₀ v₁ C) = trB v₀ v₁ ((I.toBinary v₀ v₁).soloStep p C) := by
  classical
  by_cases hp : C.pend p = none
  · have : (trB v₀ v₁ C).pend p = none := by simp [trB, hp]
    simp [soloStep, hp, this]
  · have hp' : (trB v₀ v₁ C).pend p ≠ none := by simp [trB, hp]
    obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1
      ((I.toBinary v₀ v₁).step_nextLabel_isSome C p hp)
    have e1 : (I.toBinary v₀ v₁).soloStep p C = C' := by simp [soloStep, hp, hC']
    rw [e1]
    obtain ⟨ℓ', hr, hs⟩ := toBinary_step I v₀ v₁ hC'
    suffices hℓ : I.nextLabel (trB v₀ v₁ C) p = ℓ' by simp [soloStep, hp', hℓ, hs]
    rcases ha : I.act p (C.loc p) with ⟨i, o, k⟩ | ⟨r, l⟩
    · have hn : (I.toBinary v₀ v₁).nextLabel C p = .tau p := by
        unfold nextLabel; rw [toBinary_act_access I v₀ v₁ ha]
      rw [hn] at hr; simp only [LblRel] at hr; subst hr
      unfold nextLabel; simp only [trB]; rw [ha]
    · have hn : (I.toBinary v₀ v₁).nextLabel C p = .ret p (dec v₁ r) := by
        unfold nextLabel; rw [toBinary_act_ret I v₀ v₁ ha]
      rw [hn] at hr; obtain ⟨r', rfl, -⟩ := hr
      obtain ⟨-, -, -, l', ha', -⟩ := step_ret hs
      simp only [trB] at ha'
      rw [ha] at ha'; simp only [Action.ret.injEq] at ha'
      unfold nextLabel; simp only [trB]; rw [ha, ha'.1]

/-- One-shot obstruction-freedom transfers to the binary algorithm. -/
theorem oneShotOF_toBinary (hof : I.OneShotOF) : (I.toBinary v₀ v₁).OneShotOF := by
  intro α C p hα h1 hp
  obtain ⟨α', hrel, hrun⟩ := toBinary_runFrom I v₀ v₁ hα
  obtain ⟨K, hK⟩ := hof α' (trB v₀ v₁ C) p hrun (oneShot_rel v₀ v₁ hrel h1) (by simp [trB, hp])
  refine ⟨K, ?_⟩
  have key : ∀ k (D : Config BinCons B P L),
      (I.soloStep p)^[k] (trB v₀ v₁ D) = trB v₀ v₁ (((I.toBinary v₀ v₁).soloStep p)^[k] D) := by
    intro k
    induction k with
    | zero => intro D; rfl
    | succ k ih =>
      intro D
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, toBinary_soloStep, ih]
  rw [key] at hK
  simpa [trB] using hK

end Impl

end Cslib.SharedMemory
