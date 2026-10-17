/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.PartialSync.FLM
public import Cslib.Computability.Distributed.Byzantine.PartialSync.Auth

/-!
# Covering systems with time-dependent neighbourhoods and uniform message delay

A generalization of the covering systems `Cslib.Byzantine.PartialSync.CoverSystem` of `FLM.lean`
to **synchronous runs in which every batch has the same delay**. A `DCover P Q VI` is a network of
*nodes* `x : Q`; node `x` runs the code of process `proc x` with proposal `inp x`, and at every
time `σ` it listens, as messages from sender `q`, to what node `nbr σ x q` sends at time `σ`
(nothing if `nbr σ x q = none`). With delivery offset `e` (a batch sent at `σ` is delivered at
`σ + e`, i.e. it is visible in the state at time `σ + e + 1`: *effective delay* `e + 1`), the
node states `DCover.st A e C τ x` are computed independently of any run.

## Main statements

* `DCover.run`: the run in which every faulty process `q` sends to `p` what node
  `nbr σ (lift p) q` sends, all batches delivered with offset `e`.
* `DCover.st_run` (covering lemma): if `lift` is compatible with `nbr` on correct processes, the
  correct processes have the states of their lifts; `DCover.decides_run_iff`.
* `DCover.st_eq_of_level` (locality): two systems that agree near a node have the same states at
  that node for a while; the "distance" is measured by a level function, one level per message
  delay.
* `DCover.token_origin`, `DCover.run_authValid`: with unforgeable signatures, every token emitted
  by a node was first emitted by a node of its signer; hence the covering run respects
  unforgeability if every correct process has a unique node (in a part of the system closed under
  `nbr`).
* `CoverSystem.toDCover`, `CoverSystem.st_toDCover`: the covering systems of `FLM.lean` are the
  special case `e = 0` with total, time-independent neighbourhoods.
-/

@[expose] public section

namespace Cslib.Byzantine.PartialSync

open Finset

/-- A covering system with time-dependent neighbourhoods: node `x` runs the code of `proc x` with
proposal `inp x` and receives, as the messages sent by `q` at time `σ`, what node `nbr σ x q`
sends at time `σ` (nothing for `none`). -/
structure DCover (P Q VI : Type*) where
  /-- The process whose code node `x` runs. -/
  proc : Q → P
  /-- The proposal of node `x`. -/
  inp : Q → VI
  /-- `nbr σ x q`: the node whose messages sent at time `σ` node `x` receives as messages from
  `q`. -/
  nbr : ℕ → Q → P → Option Q

namespace DCover

variable {P Q M S VI VO K : Type*} (A : Algorithm P M S VI VO) (e : ℕ) (C : DCover P Q VI)

/-- The states of the nodes of a covering system, when every batch sent at `σ` is processed in
the step at `σ + e`. -/
def st : ℕ → Q → S
  | 0, x => A.init (C.proc x) (C.inp x)
  | τ + 1, x => A.step (C.proc x) (st τ x) fun q =>
      if e ≤ τ then (C.nbr (τ - e) x q).elim [] fun y => A.send q (st (τ - e) y) (C.proc x)
      else []
termination_by τ => τ
decreasing_by all_goals omega

/-- What a node `o` (if any) sends at time `σ` to `r`, running the code of `q`. -/
def msg (o : Option Q) (q : P) (σ : ℕ) (r : P) : List M :=
  o.elim [] fun y => A.send q (C.st A e σ y) r

/-- Nobody sends nothing. -/
@[simp] theorem msg_none (q : P) (σ : ℕ) (r : P) : C.msg A e none q σ r = [] := rfl

/-- What node `y` sends. -/
@[simp] theorem msg_some (y : Q) (q : P) (σ : ℕ) (r : P) :
    C.msg A e (some y) q σ r = A.send q (C.st A e σ y) r := rfl

/-- Initial states. -/
@[simp] theorem st_zero (x : Q) : C.st A e 0 x = A.init (C.proc x) (C.inp x) := by
  rw [st]

/-- One step: a node processes the batches sent `e` time units earlier by its neighbours. -/
theorem st_succ (τ : ℕ) (x : Q) :
    C.st A e (τ + 1) x = A.step (C.proc x) (C.st A e τ x) fun q =>
      if e ≤ τ then C.msg A e (C.nbr (τ - e) x q) q (τ - e) (C.proc x) else [] := by
  rw [st]; rfl

/-- **Locality.** Let `lvl : Q → ℕ` be a level function and `T` a horizon. If the two systems
have the same code, the same proposals at nodes `x` with `(e+1) * lvl x < T`, and the same
neighbours of `x` at times `σ` with `σ + (e+1) * (lvl x + 1) < T`, these neighbours having level
`≤ lvl x + 1`, then every node `x` has the same state in both systems at times `τ` with
`τ + (e+1) * lvl x < T`. -/
theorem st_eq_of_level {C' : DCover P Q VI} (hp : C'.proc = C.proc) (lvl : Q → ℕ) (T : ℕ)
    (hn : ∀ σ x q, σ + (e + 1) * (lvl x + 1) < T →
      C'.nbr σ x q = C.nbr σ x q ∧ ∀ y, C.nbr σ x q = some y → lvl y ≤ lvl x + 1)
    (hi : ∀ x, (e + 1) * lvl x < T → C'.inp x = C.inp x) :
    ∀ τ x, τ + (e + 1) * lvl x < T → C'.st A e τ x = C.st A e τ x := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro x hx
    rcases τ with _ | τ
    · simp only [st_zero, hp, hi x (by omega)]
    · rw [st_succ, st_succ, hp, ih τ (by omega) x (by omega)]
      congr 1
      funext q
      split_ifs with he
      · have hσ : τ - e + (e + 1) * (lvl x + 1) < T := by
          rw [Nat.mul_add]; omega
        obtain ⟨h1, h2⟩ := hn (τ - e) x q hσ
        rw [h1]
        cases hy : C.nbr (τ - e) x q with
        | none => rfl
        | some y =>
          simp only [msg_some]
          rw [ih (τ - e) (by omega) y]
          have := Nat.mul_le_mul_left (e + 1) (h2 y hy)
          rw [Nat.mul_add] at hσ this
          omega
      · rfl

/-! ### Runs with uniform delivery offset -/

variable [DecidableEq P]

/-- The run in which the processes of `F` are Byzantine and every Byzantine `q` sends to `p` (at
time `σ`) what node `nbr σ (lift p) q` sends; every batch is delivered with offset `e`. -/
def run (F : Finset P) (lift : P → Q) : Run P M VI where
  faulty := F
  inp p := C.inp (lift p)
  gst := 0
  byz q σ p := C.msg A e (C.nbr σ (lift p) q) q σ p
  dl _ σ _ := σ + e

omit [DecidableEq P] in
/-- The faulty processes of the covering run. -/
@[simp] theorem run_faulty (F : Finset P) (lift : P → Q) : (C.run A e F lift).faulty = F := rfl

omit [DecidableEq P] in
/-- The proposals of the covering run are those of the lifts. -/
@[simp] theorem run_inp (F : Finset P) (lift : P → Q) (p : P) :
    (C.run A e F lift).inp p = C.inp (lift p) := rfl

/-- **Covering lemma.** Let `X` be a set of processes, each running the code of its lift and
listening to the lifts of the correct processes, which belong to `X`. Then the processes of `X`
(correct or not) have the states of their lifts. -/
theorem st_run {F : Finset P} {lift : P → Q} (X : Set P)
    (hX : ∀ p ∈ X, C.proc (lift p) = p ∧
      ∀ q ∉ F, q ∈ X ∧ ∀ σ, C.nbr σ (lift p) q = some (lift q)) :
    ∀ τ, ∀ p ∈ X, (C.run A e F lift).st A τ p = C.st A e τ (lift p) := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro p hp
    obtain ⟨hpr, hq⟩ := hX p hp
    rcases τ with _ | τ
    · simp [hpr, run]
    · rw [Run.st_succ, st_succ, hpr, ih τ (by omega) p hp]
      congr 1
      funext q
      rw [Run.inbox_of_dl_eq_add A (fun _ => rfl)]
      split_ifs with he
      · by_cases hqF : q ∈ F
        · rw [Run.out_of_faulty A _ hqF]; rfl
        · obtain ⟨hqX, hn⟩ := hq q hqF
          rw [Run.out_of_correct A _ hqF, ih (τ - e) (by omega) q hqX, hn, msg_some]
      · rfl

/-- The covering lemma for the correct processes. -/
theorem st_run_correct {F : Finset P} {lift : P → Q}
    (hcov : ∀ p ∉ F, C.proc (lift p) = p ∧ ∀ q ∉ F, ∀ σ, C.nbr σ (lift p) q = some (lift q)) :
    ∀ τ, ∀ p ∉ F, (C.run A e F lift).st A τ p = C.st A e τ (lift p) := fun τ p hp =>
  C.st_run A e {p | p ∉ F}
    (fun p hp => ⟨(hcov p hp).1, fun q hq => ⟨hq, (hcov p hp).2 q hq⟩⟩) τ p hp

/-- Correct processes decide in the covering run as their lifts do in the system. -/
theorem decides_run_iff {F : Finset P} {lift : P → Q}
    (hcov : ∀ p ∉ F, C.proc (lift p) = p ∧ ∀ q ∉ F, ∀ σ, C.nbr σ (lift p) q = some (lift q))
    {p : P} (hp : p ∉ F) {v : VO} :
    (C.run A e F lift).Decides A p v ↔ ∃ τ, A.decide p (C.st A e τ (lift p)) = some v := by
  simp only [Run.Decides, C.st_run_correct A e hcov _ p hp]

/-! ### Signatures -/

/-- **Nodes are unforging**: a token sent by node `x` is signed by `proc x` or was received
before, from a neighbour. -/
theorem node_unforging [Finite P] {Au : Auth P M K} (hU : A.Unforging Au) (x : Q) (τ : ℕ)
    (r : P) (m : M) (hm : m ∈ A.send (C.proc x) (C.st A e τ x) r) (t : K)
    (ht : t ∈ Au.tokens m) :
    Au.signer t = C.proc x ∨ ∃ σ < τ, ∃ q y, C.nbr σ x q = some y ∧
      ∃ m' ∈ A.send q (C.st A e σ y) (C.proc x), t ∈ Au.tokens m' := by
  have := Fintype.ofFinite P
  set R := C.run A e univ (fun _ => x)
  have hst := C.st_run A e (F := univ) (lift := fun _ => x) {C.proc x}
    (fun p hp => ⟨by simp only [Set.mem_singleton_iff] at hp; exact hp.symm,
      fun q hq => absurd (mem_univ q) hq⟩) τ (C.proc x) rfl
  rw [← hst] at hm
  rcases hU R (C.proc x) τ r m hm t ht with h | ⟨τ', hτ', q, m', hm', ht'⟩
  · exact Or.inl h
  · obtain ⟨σ, hσ, -, hm''⟩ := Run.mem_inbox.mp hm'
    rw [Run.out_of_faulty A _ (mem_univ q)] at hm''
    change m' ∈ C.msg A e (C.nbr σ x q) q σ (C.proc x) at hm''
    cases hy : C.nbr σ x q with
    | none => rw [hy] at hm''; simp at hm''
    | some y =>
      rw [hy, msg_some] at hm''
      exact Or.inr ⟨σ, by omega, q, y, hy, m', hm'', ht'⟩

/-- **Origin of tokens.** In a part `N` of the system closed under `nbr` (where neighbours run
the code of the sender they stand for), every token sent by a node was emitted earlier by a node
of `N` running the code of its signer. -/
theorem token_origin [Finite P] {Au : Auth P M K} (hU : A.Unforging Au) (N : Set Q)
    (hN : ∀ x ∈ N, ∀ σ q y, C.nbr σ x q = some y → y ∈ N ∧ C.proc y = q) :
    ∀ τ, ∀ x ∈ N, ∀ r, ∀ m ∈ A.send (C.proc x) (C.st A e τ x) r, ∀ t ∈ Au.tokens m,
      ∃ z ∈ N, C.proc z = Au.signer t ∧ ∃ σ ≤ τ, ∃ r', ∃ m' ∈ A.send (C.proc z) (C.st A e σ z) r',
        t ∈ Au.tokens m' := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro x hx r m hm t ht
    rcases C.node_unforging A e hU x τ r m hm t ht with h | ⟨σ, hσ, q, y, hy, m', hm', ht'⟩
    · exact ⟨x, hx, h.symm, τ, le_rfl, r, m, hm, ht⟩
    · obtain ⟨hyN, hyp⟩ := hN x hx σ q y hy
      rw [← hyp] at hm'
      obtain ⟨z, hz, hzp, σ', hσ', r', m'', hm'', ht''⟩ := ih σ hσ y hyN _ m' hm' t ht'
      exact ⟨z, hz, hzp, σ', by omega, r', m'', hm'', ht''⟩

/-- **The covering run respects unforgeability** if, in a part `N` of the system closed under
`nbr` and containing the lifts of the correct processes, every node running the code of a
correct process is its lift. -/
theorem run_authValid [Finite P] {Au : Auth P M K} (hU : A.Unforging Au) {F : Finset P}
    {lift : P → Q}
    (hcov : ∀ p ∉ F, C.proc (lift p) = p ∧ ∀ q ∉ F, ∀ σ, C.nbr σ (lift p) q = some (lift q))
    (N : Set Q) (hN : ∀ x ∈ N, ∀ σ q y, C.nbr σ x q = some y → y ∈ N ∧ C.proc y = q)
    (hlift : ∀ p ∉ F, lift p ∈ N) (huniq : ∀ z ∈ N, C.proc z ∉ F → z = lift (C.proc z)) :
    (C.run A e F lift).AuthValid Au A := by
  intro b _ τ r hr m hm t ht
  change m ∈ C.msg A e (C.nbr τ (lift r) b) b τ r at hm
  cases hy : C.nbr τ (lift r) b with
  | none => rw [hy] at hm; simp at hm
  | some y =>
    rw [hy, msg_some] at hm
    obtain ⟨hyN, hyp⟩ := hN _ (hlift r hr) τ b y hy
    rw [← hyp] at hm
    obtain ⟨z, hz, hzp, σ, hσ, r', m', hm', ht'⟩ := C.token_origin A e hU N hN τ y hyN r m hm t ht
    by_cases hsF : Au.signer t ∈ F
    · exact Or.inl hsF
    · right
      have hzl : z = lift (Au.signer t) := hzp ▸ huniq z hz (hzp ▸ hsF)
      refine ⟨σ, hσ, Au.signer t, hsF, r', m', ?_, ht'⟩
      rw [Run.out_of_correct A _ hsF, C.st_run_correct A e hcov σ _ hsF, ← hzl, ← hzp]
      exact hm'

end DCover

/-- A covering system of `FLM.lean` as a `DCover`: offset `e = 0`, total and time-independent
neighbourhoods. -/
def CoverSystem.toDCover {P Q VI : Type*} (C : CoverSystem P Q VI) : DCover P Q VI where
  proc := C.proc
  inp := C.inp
  nbr _ x q := some (C.nbr x q)

/-- The states of a covering system are those of its `DCover` with offset `0`. -/
theorem CoverSystem.st_toDCover {P Q M S VI VO : Type*} (A : Algorithm P M S VI VO)
    (C : CoverSystem P Q VI) : ∀ τ x, C.toDCover.st A 0 τ x = C.st A τ x := by
  intro τ
  induction τ with
  | zero => intro x; simp [toDCover]
  | succ τ ih =>
    intro x
    rw [DCover.st_succ, CoverSystem.st_succ, ih]
    congr 1
    funext q
    simp only [Nat.zero_le, ite_true, Nat.sub_zero]
    exact congrArg (fun s => A.send q s (C.proc x)) (ih _)

end Cslib.Byzantine.PartialSync
