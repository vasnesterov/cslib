/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.Constructions
public import Mathlib.Computability.Partrec
public import Mathlib.Data.Fintype.Pi

/-!
# Computable algorithms and their canonical decisions

Characterizations of solvable agreement problems ("there is a Turing-computable `Λ` mapping
every input configuration to an admissible decision") need the decision of an algorithm in the
canonical synchronous run of a configuration (`canonRun c d`) as a *computable* function of the
configuration. We use Mathlib's notion `Computable` (partial recursive and total, via
`Primcodable` encodings). Processes are `Fin n`, so that `Config (Fin n) VI` is `Primcodable`
(`Primcodable.finArrow`) as soon as `VI` is.

## Main definitions

* `Algorithm.lockStep A c d`: explicit lock-step simulation of the canonical run `canonRun c d`
  (`canonRun_st_eq_lockStep`).
* `Algorithm.IsComputable A`: `init`, `step`, `send` and `decide` are computable.
* `Algorithm.decAt A d c k`: the decision at time `k.unpair.1` of the process encoded by
  `k.unpair.2`, if it belongs to `π(c)`, in the canonical run of `c`.

## Main statements

* `Algorithm.lockStep_computable`: the lock-step simulation of a computable algorithm is
  computable in the configuration and the time.
* `Algorithm.IsComputable.exists_computable_canonDecision`: if a computable algorithm
  terminates in the canonical runs of all input configurations, then some *computable* `Λ` maps
  every input configuration `c` to a value decided by a process of `π(c)` in the canonical run of
  `c` (`Λ c` is the first decision found by unbounded search, `Nat.rfindOpt`).
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

open Finset

/-! ### The lock-step simulation -/

section LockStep

variable {P M S VI VO : Type*}

/-- Explicit lock-step simulation of the canonical synchronous run of configuration `c`
(dummy proposal `d` outside `π(c)`): at every time each process receives exactly the messages
sent at that time by the processes of `π(c)`. -/
def Algorithm.lockStep (A : Algorithm P M S VI VO) (c : Config P VI) (d : VI) : ℕ → P → S
  | 0 => fun p => A.init p ((c p).getD d)
  | τ + 1 => fun p => A.step p (A.lockStep c d τ p)
      (fun q => if c q = none then [] else A.send q (A.lockStep c d τ q) p)

variable [Fintype P] [DecidableEq P]

/-- The canonical run is the lock-step simulation. -/
theorem canonRun_st_eq_lockStep (A : Algorithm P M S VI VO) (c : Config P VI) (d : VI)
    (τ : ℕ) : (canonRun (M := M) c d).st A τ = A.lockStep c d τ := by
  induction τ with
  | zero => funext p; simp [Algorithm.lockStep, canonRun]
  | succ τ ih =>
    funext p
    rw [Run.st_succ, ih]
    simp only [Algorithm.lockStep]
    congr 1
    funext q
    rw [Run.inbox_eq_flatMap, List.range_succ, List.flatMap_append]
    have h1 : ((List.range τ).flatMap fun τ' => (canonRun (M := M) c d).dlv A q τ' p τ) = [] := by
      refine List.flatMap_eq_nil_iff.mpr fun τ' hτ' => ?_
      simp only [List.mem_range] at hτ'
      exact Run.dlv_eq_nil_of_ne _ _ (by simp [canonRun]; omega)
    rw [h1]
    have hdl : (canonRun (M := M) c d).dl q τ p = τ := rfl
    simp only [List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, Run.dlv,
      hdl, ite_true]
    by_cases hq : c q = none
    · rw [Run.out_of_faulty _ _ (by simp [canonRun, hq])]; simp [hq, canonRun]
    · rw [Run.out_of_correct _ _ (by simp [canonRun, Option.isSome_iff_ne_none, hq]), ih]
      simp [hq]

end LockStep

/-! ### Computable algorithms -/

section Computable

variable {n : ℕ} {M S VI VO : Type*} [Primcodable M] [Primcodable S] [Primcodable VI]
  [Primcodable VO]

/-- An algorithm on processes `Fin n` is *computable* if it is a computable state machine:
the initial state (as a function of process and proposal), the transition function (of process,
state and received messages), the outgoing messages (of sender, state and receiver) and the
decision (of process and state) are all `Computable`. -/
structure Algorithm.IsComputable (A : Algorithm (Fin n) M S VI VO) : Prop where
  init : Computable₂ A.init
  step : Computable fun x : Fin n × S × (Fin n → List M) => A.step x.1 x.2.1 x.2.2
  send : Computable fun x : Fin n × S × Fin n => A.send x.1 x.2.1 x.2.2
  decide : Computable₂ A.decide

omit [Primcodable M] [Primcodable S] [Primcodable VI] [Primcodable VO] in
/-- A function into `Fin n → σ` is computable if all its components are. -/
theorem _root_.Computable.finArrow_of {α σ : Type*} [Primcodable α] [Primcodable σ]
    {f : α → Fin n → σ} (h : ∀ i, Computable fun a => f a i) : Computable f :=
  (Primrec.vector_get'.to_comp.comp (Computable.vector_ofFn h)).of_eq fun a => by
    funext i; simp

variable {A : Algorithm (Fin n) M S VI VO}

/-- The lock-step simulation of a computable algorithm is computable (in the configuration and
the time). -/
theorem Algorithm.lockStep_computable (hA : A.IsComputable) (d : VI) :
    Computable fun x : Config (Fin n) VI × ℕ => A.lockStep x.1 d x.2 := by
  open Computable in
  have key : ∀ x : Config (Fin n) VI × ℕ, A.lockStep x.1 d x.2 =
      Nat.rec (motive := fun _ => Fin n → S) (fun p => A.init p ((x.1 p).getD d))
        (fun _ IH p => A.step p (IH p)
          (fun q => bif (x.1 q).isSome then A.send q (IH q) p else [])) x.2 := by
    rintro ⟨c, τ⟩
    induction τ with
    | zero => rfl
    | succ τ ih =>
      simp only [Algorithm.lockStep] at ih ⊢
      rw [ih]
      funext p
      congr 1
      funext q
      cases c q <;> rfl
  open Computable in
  refine (nat_rec (f := fun x : Config (Fin n) VI × ℕ => x.2)
    (g := fun x p => A.init p ((x.1 p).getD d))
    (h := fun x y p => A.step p (y.2 p)
          (fun q => bif (x.1 q).isSome then A.send q (y.2 q) p else [])) snd
    (finArrow_of fun p => hA.init.comp (const p)
      (option_getD (fin_app.comp fst (const p)) (const d)))
    (finArrow_of fun p => hA.step.comp (pair (const p) (pair (fin_app.comp (snd.comp snd) (const p))
      (finArrow_of fun q => cond (Primrec.option_isSome.to_comp.comp
          (fin_app.comp (fst.comp fst) (const q)))
        (hA.send.comp (pair (const q) (pair (fin_app.comp (snd.comp snd) (const q)) (const p))))
        (const []))))).to₂).of_eq fun x => (key x).symm

/-- The search space for canonical decisions: index `k = ⟪τ, i⟫` asks for the decision at time `τ`
of the process encoded by `i`, if it belongs to `π(c)`, in the lock-step canonical run of `c`. -/
def Algorithm.decAt (A : Algorithm (Fin n) M S VI VO) (d : VI) (c : Config (Fin n) VI) (k : ℕ) :
    Option VO :=
  (Encodable.decode (α := Fin n) k.unpair.2).bind fun p =>
    bif (c p).isSome then A.decide p (A.lockStep c d k.unpair.1 p) else none

theorem Algorithm.decAt_computable (hA : A.IsComputable) (d : VI) : Computable₂ (A.decAt d) := by
  open Computable in
  exact option_bind (Computable.decode.comp (snd.comp (unpair.comp snd)))
    (cond (Primrec.option_isSome.to_comp.comp (fin_app.comp (fst.comp fst) snd))
      (hA.decide.comp snd (fin_app.comp ((Algorithm.lockStep_computable hA d).comp
        (pair (fst.comp fst) (fst.comp (unpair.comp (snd.comp fst))))) snd))
      (const none)).to₂

omit [Primcodable M] [Primcodable S] [Primcodable VI] [Primcodable VO] in
theorem Algorithm.decAt_spec {d : VI} {c : Config (Fin n) VI} {k : ℕ} {v : VO}
    (h : A.decAt d c k = some v) :
    ∃ p, c p ≠ none ∧ (canonRun (M := M) c d).Decides A p v := by
  unfold Algorithm.decAt at h
  obtain ⟨p, -, hp⟩ := Option.bind_eq_some_iff.mp h
  cases hcp : c p with
  | none => simp [hcp] at hp
  | some w =>
    refine ⟨p, by simp [hcp], k.unpair.1, ?_⟩
    rw [canonRun_st_eq_lockStep]
    simpa [hcp] using hp

/-- **Computable canonical decisions.** If a computable algorithm terminates (at every process of
`π(c)`) in the canonical run of every input configuration `c`, and `t < n`, then some computable
`Λ` maps every input configuration `c` to a value decided by a process of `π(c)` in the canonical
run of `c`. `Λ c` is the first decision found by unbounded search over (time, process) pairs; to
make `Λ` total, a configuration that is not an input configuration is first replaced by the
failure-free configuration with all proposals `d`. -/
theorem Algorithm.IsComputable.exists_computable_canonDecision (hA : A.IsComputable) (d : VI)
    {t : ℕ} (htn : t < n)
    (hterm : ∀ c, IsInputConfig t c → ∀ p, c p ≠ none →
      ∃ v, (canonRun (M := M) c d).Decides A p v) :
    ∃ Λ : Config (Fin n) VI → VO, Computable Λ ∧
      ∀ c, IsInputConfig t c → ∃ p, c p ≠ none ∧ (canonRun (M := M) c d).Decides A p (Λ c) := by
  classical
  let c₀ : Config (Fin n) VI := fun _ => some d
  let norm : Config (Fin n) VI → Config (Fin n) VI := fun c =>
    if IsInputConfig t c then c else c₀
  have hnorm : ∀ c, IsInputConfig t (norm c) := by
    intro c
    by_cases h : IsInputConfig t c
    · simp [norm, h]
    · simp only [norm, h, ite_false]
      unfold IsInputConfig; simp [Config.procs, c₀]
  have hnormc : Computable norm := by
    open Computable in
    let F : (Fin n → Bool) → Bool := fun b =>
      Decidable.decide (n - t ≤ (univ.filter fun i => b i).card)
    refine (cond ((Primrec.dom_finite F).to_comp.comp
      (finArrow_of fun i => Primrec.option_isSome.to_comp.comp (fin_app.comp .id (const i))))
      .id (const c₀)).of_eq fun c => ?_
    simp [norm, F, IsInputConfig, Config.procs]
  have hdom : ∀ c, IsInputConfig t c → (Nat.rfindOpt (A.decAt d c)).Dom := by
    intro c hc'
    obtain ⟨p, hp⟩ : c.procs.Nonempty :=
      card_pos.mp (by unfold IsInputConfig at hc'; simp at hc'; omega)
    obtain ⟨v, τ, hv⟩ := hterm c hc' p (Config.mem_procs_iff_ne_none.mp hp)
    rw [canonRun_st_eq_lockStep] at hv
    refine Nat.rfindOpt_dom.mpr ⟨Nat.pair τ (Encodable.encode p), v, ?_⟩
    simp only [Config.mem_procs] at hp
    simp [Algorithm.decAt, Nat.unpair_pair, Encodable.encodek, hp, hv]
  have hpart : Partrec fun c => Nat.rfindOpt (A.decAt d (norm c)) :=
    Partrec.rfindOpt ((Algorithm.decAt_computable hA d).comp (hnormc.comp .fst) .snd)
  refine ⟨fun c => (Nat.rfindOpt (A.decAt d (norm c))).get (hdom _ (hnorm c)),
    hpart.of_eq_tot fun c => Part.get_mem _, fun c hc' => ?_⟩
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec (Part.get_mem (hdom _ (hnorm c)))
  beta_reduce
  generalize (Nat.rfindOpt (A.decAt d (norm c))).get _ = v at hk ⊢
  rw [show norm c = c from ite_eq_left_iff.mpr fun h => absurd hc' h] at hk
  exact Algorithm.decAt_spec hk

end Computable

end Cslib.Byzantine.PartialSync
