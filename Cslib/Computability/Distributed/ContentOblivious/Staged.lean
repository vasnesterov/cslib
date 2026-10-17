/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Computability.Distributed.ContentOblivious.Compose
public import Mathlib.Tactic.Ring

/-!
# Running composable procedures back-to-back (staged programs)

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026, §4 (Theorem 9: a procedure with the composable ending property can be followed by any
other procedure).

A *driver* runs a sequence of *stages* at every node: each stage is one execution of a procedure
`P : Proc J R`; when a node returns `r` from a stage, its driver updates a local state `d : D` and
either starts the next stage (with an input computed from `d` and `r`) or halts. Pulses carry no
content, so a node cannot tell from which stage a pulse comes.

`staged_final` / `staged_totalSent`: if every stage is `Composable` (see `Compose.lean`) and the
stage results follow a fixed synchronous schedule (`d k`, `j k`, `r k`: driver states, stage inputs
and stage results in stage `k`), then every execution of the staged program behaves as the stages
run one after the other: every final configuration is quiescent with every node halted in its
final driver state `d K`, and the pulse count is at most the sum of the per-stage bounds.

The proof keeps, for every configuration of the staged program, one configuration `C k` of each
stage (`Inv`); a node in stage `k` that reads a pulse always reads a pulse of stage `k`: earlier
stages are quiescent at that node (it has returned from them), and later stages have not reached
the link unless the neighbour already returned from stage `k`, in which case `clean` provides a
pulse of stage `k` in transit.
-/

@[expose] public section

namespace Cslib.ContentOblivious

open Finset

variable {V : Type*} [DecidableEq V]

/-! ## Basic facts about executions of programs -/

namespace Prog

variable {I : Type*} [Encodable I] [Inhabited I] {P : Prog I} {W : Wiring V}

/-- A terminated node keeps its state and counters along a step. -/
lemma step_st_ne {c c' : Config V P.State} (h : P.Step W c c') {w : V}
    (hw : P.terminated (c.st w) = true) : c'.st w = c.st w ∧ ∀ q, c'.recvd (w, q) = c.recvd (w, q) ∧
      c.sent (w, q) = c'.sent (w, q) := by
  obtain ⟨v, j, hen⟩ := h
  have hne : w ≠ v := by
    rintro rfl; have := hen.1; simp [hw] at this
  refine ⟨deliver_st_ne _ _ _ _ hne, fun q => ⟨?_, ?_⟩⟩
  · rw [deliver_recvd]; simp [hne]
  · rw [deliver_sent]; simp [hne]

/-- Termination is stable along a step. -/
lemma step_terminated {c c' : Config V P.State} (h : P.Step W c c') {w : V}
    (hw : P.terminated (c.st w) = true) : P.terminated (c'.st w) = true := by
  rw [(step_st_ne h hw).1]; exact hw

/-- Along an execution, a terminated node keeps its state and its received counters, and the
pulse counters never decrease. -/
lemma steps_frozen {c c' : Config V P.State} (h : Relation.ReflTransGen (P.Step W) c c') {w : V}
    (hw : P.terminated (c.st w) = true) :
    c'.st w = c.st w ∧ (∀ q, c'.recvd (w, q) = c.recvd (w, q)) := by
  induction h with
  | refl => exact ⟨rfl, fun _ => rfl⟩
  | @tail b _ _ hs ih =>
    have ht : P.terminated (b.st w) = true := by rw [ih.1]; exact hw
    obtain ⟨h1, h2⟩ := step_st_ne hs ht
    exact ⟨h1.trans ih.1, fun q => ((h2 q).1).trans (ih.2 q)⟩

/-- Sent counters only grow along executions. -/
lemma steps_sent_mono {c c' : Config V P.State} (h : Relation.ReflTransGen (P.Step W) c c') :
    ∀ p, c.sent p ≤ c'.sent p := by
  induction h with
  | refl => exact fun _ => le_rfl
  | tail _ hs ih => exact fun p => (ih p).trans (Step.sent_le hs p)

/-- Reachability is closed under executions. -/
lemma Reach.trans_steps {x : V → I} {c c' : Config V P.State} (h : P.Reach W x c)
    (h' : Relation.ReflTransGen (P.Step W) c c') : P.Reach W x c' :=
  Relation.ReflTransGen.trans h h'

/-- No more pulses are received than sent, for programs. -/
lemma Reach.recvd_le' {x : V → I} {c : Config V P.State} (h : P.Reach W x c) :
    ∀ p, c.recvd p ≤ c.sent (W.peer p) := Cslib.ContentOblivious.Reach.recvd_le h

end Prog

namespace Proc

/-- A procedure has terminated iff it has returned. -/
lemma terminated_iff {J R : Type*} {P : Proc J R} (s : P.State) :
    P.terminated s = true ↔ (P.result s).isSome := by
  rw [P.terminated_eq]

variable [Fintype V] {J R : Type*} [Encodable J] [Inhabited J] {P : Proc J R} {W : Wiring V}
  {x : V → J}

/-- A composable procedure: a node that has returned has consumed every pulse ever sent to it. -/
lemma Composable.recvd_eq (hP : P.Composable W x) {c : Config V P.State} (hc : P.Reach W x c)
    {v : V} (hv : (P.result (c.st v)).isSome) (q : Bool) :
    c.recvd (v, q) = c.sent (W.peer (v, q)) := by
  obtain ⟨B, hB⟩ := hP.bounded
  obtain ⟨c', hcc', hfin⟩ := exists_final hB hc
  have hr' : P.Reach W x c' := Prog.Reach.trans_steps hc hcc'
  have ht : P.terminated (c.st v) = true := (terminated_iff _).2 hv
  have hfr := Prog.steps_frozen hcc' ht
  have hq := (hP.final c' hr' hfin).1 (v, q)
  have h1 := Prog.steps_sent_mono hcc' (W.peer (v, q))
  have h2 := hc.recvd_le' (v, q)
  rw [hfr.2 q] at hq
  omega

/-- The results announced by `Returns` are already fixed when a node returns. -/
lemma Composable.result_eq (hP : P.Composable W x) {r : V → R} (hret : P.Returns W x r)
    {c : Config V P.State} (hc : P.Reach W x c) {v : V} {a : R} (hv : P.result (c.st v) = some a) :
    a = r v := by
  obtain ⟨B, hB⟩ := hP.bounded
  obtain ⟨c', hcc', hfin⟩ := exists_final hB hc
  have hr' : P.Reach W x c' := Prog.Reach.trans_steps hc hcc'
  have ht : P.terminated (c.st v) = true := (terminated_iff _).2 (by rw [hv]; rfl)
  have := hret c' hr' hfin v
  rw [(Prog.steps_frozen hcc' ht).1, hv] at this
  exact Option.some_injective _ this

end Proc

/-! ## Drivers and staged programs -/

/-- A driver: initial local state and first stage input, and, after a stage returned a result,
the new local state and the next stage input (`none` = halt). -/
structure Driver (I J R D : Type*) where
  /-- The initial local state and first stage input (`none` = halt), from the node's input. -/
  start : I → D × Option J
  /-- The new local state and next stage input after a stage returned a result. -/
  next : D → R → D × Option J

namespace Proc

variable {I J R D : Type} (P : Proc J R)

/-- Start the stage with input `oj` (or halt), with local state `d`. -/
def launch (d : D) : Option J → (D × Option P.State) × (Bool → ℕ)
  | none => ((d, none), fun _ => 0)
  | some j => ((d, some (P.init j).1), (P.init j).2)

/-- Reaction of a staged node running stage state `s` with local state `d`. -/
def stagedRecv (dr : Driver I J R D) (d : D) (s : P.State) (q : Bool) :
    (D × Option P.State) × (Bool → ℕ) :=
  match P.result (P.recv s q).1 with
  | none => ((d, some (P.recv s q).1), (P.recv s q).2)
  | some r =>
    ((P.launch (dr.next d r).1 (dr.next d r).2).1,
      fun p => (P.recv s q).2 p + (P.launch (dr.next d r).1 (dr.next d r).2).2 p)

/-- The staged program: run stages of `P` as directed by the driver `dr`. Its result is the
final local state. -/
@[reducible] def staged (dr : Driver I J R D) : Proc I D where
  State := D × Option P.State
  init i := P.launch (dr.start i).1 (dr.start i).2
  recv st q := match st with
    | (d, none) => ((d, none), fun _ => 0)
    | (d, some s) => P.stagedRecv dr d s q
  ready st q := match st with
    | (_, none) => false
    | (_, some s) => P.ready s q
  terminated st := st.2.isNone
  result st := match st with
    | (d, none) => some d
    | (_, some _) => none
  terminated_eq st := by rcases st with ⟨d, _ | s⟩ <;> rfl

variable {P}

/-- A staged node starts by launching the first stage of its driver. -/
@[simp] lemma staged_init (dr : Driver I J R D) (i : I) :
    (P.staged dr).init i = P.launch (dr.start i).1 (dr.start i).2 := rfl
/-- A node in a stage reacts as the stage procedure. -/
@[simp] lemma staged_recv_some (dr : Driver I J R D) (d : D) (s : P.State) (q : Bool) :
    (P.staged dr).recv (d, some s) q = P.stagedRecv dr d s q := rfl
/-- A node in a stage reads as the stage procedure. -/
@[simp] lemma staged_ready_some (dr : Driver I J R D) (d : D) (s : P.State) (q : Bool) :
    (P.staged dr).ready (d, some s) q = P.ready s q := rfl
/-- A halted node never reads. -/
@[simp] lemma staged_ready_none (dr : Driver I J R D) (d : D) (q : Bool) :
    (P.staged dr).ready (d, none) q = false := rfl
/-- A staged node is terminated iff it has halted. -/
@[simp] lemma staged_terminated (dr : Driver I J R D) (st : D × Option P.State) :
    (P.staged dr).terminated st = st.2.isNone := rfl
/-- A halted node returns its driver state. -/
@[simp] lemma staged_result_none (dr : Driver I J R D) (d : D) :
    (P.staged dr).result (d, none) = some d := rfl
/-- A node in a stage has not returned. -/
@[simp] lemma staged_result_some (dr : Driver I J R D) (d : D) (s : P.State) :
    (P.staged dr).result (d, some s) = none := rfl

end Proc

/-! ## The synchronous schedule and the decomposition invariant -/

section staged

variable [Fintype V] {I J R D : Type} [Encodable I] [Inhabited I] [Encodable J] [Inhabited J]

/-- The synchronous schedule of a staged execution: `K` stages; in stage `k < K` node `v` has
local state `d k v`, runs `P` with input `j k v` and returns `r k v`; finally it halts with local
state `d K v`. Every stage is composable and returns the scheduled results. -/
structure Schedule (P : Proc J R) (dr : Driver I J R D) (W : Wiring V) (x : V → I) (K : ℕ)
    (d : ℕ → V → D) (j : ℕ → V → J) (r : ℕ → V → R) : Prop where
  /-- No node has returned at start-up. -/
  init_none : ∀ a, P.result (P.init a).1 = none
  /-- The driver starts in the scheduled state and stage input. -/
  start : ∀ v, dr.start (x v) = (d 0 v, if 0 < K then some (j 0 v) else none)
  /-- After stage `k`, the driver moves to the scheduled state and stage input. -/
  next : ∀ k < K, ∀ v, dr.next (d k v) (r k v) =
    (d (k + 1) v, if k + 1 < K then some (j (k + 1) v) else none)
  /-- Every stage is composable. -/
  comp : ∀ k < K, P.Composable W (j k)
  /-- Every stage returns the scheduled results. -/
  ret : ∀ k < K, P.Returns W (j k) (r k)

variable {P : Proc J R} {W : Wiring V}

/-- `c` is a configuration of a stage with inputs `y` in which exactly the nodes with `k ≤ σ v`
have started: it is a reachable configuration of `P` minus the start-up pulses of the nodes that
have not started yet (which have done nothing), and no pulse was consumed before being sent. -/
def StageCfg (P : Proc J R) (W : Wiring V) (y : V → J) (σ : V → ℕ) (k : ℕ)
    (c : Config V P.State) : Prop :=
  (∃ c', P.Reach W y c' ∧ c'.st = c.st ∧ c'.recvd = c.recvd ∧
    ∀ p, c'.sent p = c.sent p + if k ≤ σ p.1 then 0 else (P.init (y p.1)).2 p.2) ∧
  (∀ v, σ v < k → c.st v = (P.init (y v)).1 ∧ ∀ q, c.recvd (v, q) = 0 ∧ c.sent (v, q) = 0) ∧
  (∀ p, c.recvd p ≤ c.sent (W.peer p))

/-- The idle configuration of a stage: nobody has started. -/
def idleCfg (P : Proc J R) (y : V → J) : Config V P.State where
  st v := (P.init (y v)).1
  sent _ := 0
  recvd _ := 0

/-- In a stage configuration, a returned node has received every pulse sent to it. -/
lemma StageCfg.recvd_eq {y : V → J} {σ : V → ℕ} {k : ℕ} {c : Config V P.State}
    (h : StageCfg P W y σ k c) (hP : P.Composable W y) {v : V} (hv : (P.result (c.st v)).isSome)
    (q : Bool) : c.recvd (v, q) = c.sent (W.peer (v, q)) := by
  obtain ⟨⟨c', hr, hst, hrc, hs⟩, -, hle⟩ := h
  have := hP.recvd_eq hr (v := v) (by rw [hst]; exact hv) q
  rw [hrc, hs] at this
  have := hle (v, q)
  split_ifs at * <;> omega

/-- In a stage configuration, returned results are the scheduled ones. -/
lemma StageCfg.result_eq {y : V → J} {σ : V → ℕ} {k : ℕ} {c : Config V P.State}
    (h : StageCfg P W y σ k c) (hP : P.Composable W y) {rr : V → R} (hret : P.Returns W y rr)
    {v : V} {a : R} (hv : P.result (c.st v) = some a) : a = rr v := by
  obtain ⟨⟨c', hr, hst, -, -⟩, -, -⟩ := h
  exact hP.result_eq hret hr (by rw [hst]; exact hv)

/-- Sum over `range K` of a function modified at one index `k < K`. -/
lemma sum_range_ite_eq {K k : ℕ} (hk : k < K) (f : ℕ → ℕ) (a : ℕ) :
    (∑ m ∈ range K, if m = k then a else f m) + f k = (∑ m ∈ range K, f m) + a := by
  have hmem : k ∈ range K := mem_range.2 hk
  rw [← add_sum_erase _ _ hmem, ← add_sum_erase _ _ hmem]
  simp only [↓reduceIte]
  have : ∑ m ∈ (range K).erase k, (if m = k then a else f m) = ∑ m ∈ (range K).erase k, f m :=
    sum_congr rfl fun m hm => by rw [ite_eq_right (ne_of_mem_erase hm)]
  rw [this]; ring

variable {dr : Driver I J R D} {x : V → I} {K : ℕ} {d : ℕ → V → D} {j : ℕ → V → J}
  {r : ℕ → V → R}

/-- Starting node `v` in a stage configuration: add its start-up pulses. -/
def startCfg (P : Proc J R) (y : V → J) (v : V) (c : Config V P.State) : Config V P.State :=
  { c with sent := fun p => c.sent p + if p.1 = v then (P.init (y v)).2 p.2 else 0 }

omit [Fintype V] in
/-- Stage configurations only depend on which nodes reached the stage. -/
lemma StageCfg.congr {y : V → J} {σ σ' : V → ℕ} {k : ℕ} {c : Config V P.State}
    (h : StageCfg P W y σ k c) (hσ : ∀ w, k ≤ σ w ↔ k ≤ σ' w) : StageCfg P W y σ' k c := by
  obtain ⟨⟨c', hr, hst, hrc, hs⟩, hun, hle⟩ := h
  refine ⟨⟨c', hr, hst, hrc, fun p => ?_⟩, fun w hw => hun w ?_, hle⟩
  · rw [hs]; congr 1; exact if_congr (hσ p.1) rfl rfl
  · have := hσ w; omega

omit [Fintype V] in
/-- Stage configurations are closed under enabled deliveries of the stage. -/
lemma StageCfg.deliver {y : V → J} {σ : V → ℕ} {k : ℕ} {c : Config V P.State}
    (h : StageCfg P W y σ k c) {v : V} {q : Bool} (hvk : k ≤ σ v)
    (hterm : P.result (c.st v) = none) (hready : P.ready (c.st v) q = true)
    (hA : c.recvd (v, q) < c.sent (W.peer (v, q))) :
    StageCfg P W y σ k (Cslib.ContentOblivious.deliver P.toAlgo c v q) := by
  obtain ⟨⟨c', hr, hst, hrc, hs⟩, hun, hle⟩ := h
  refine ⟨⟨Cslib.ContentOblivious.deliver P.toAlgo c' v q, hr.tail (Step.mk _ v q ⟨?_, ?_, ?_⟩),
    ?_, ?_, fun p => ?_⟩, fun w hw => ?_, fun p => ?_⟩
  · simp only [hst, P.terminated_eq, hterm]; rfl
  · simpa [hst] using hready
  · rw [hrc, hs]; omega
  · simp [Cslib.ContentOblivious.deliver, hst]
  · simp [Cslib.ContentOblivious.deliver, hrc]
  · simp only [deliver_sent, hs, hst]; omega
  · have hwv : w ≠ v := by rintro rfl; omega
    obtain ⟨h1, h2⟩ := hun w hw
    refine ⟨by rw [deliver_st_ne _ _ _ _ hwv, h1], fun q' => ⟨?_, ?_⟩⟩
    · rw [deliver_recvd]; simp [hwv, (h2 q').1]
    · rw [deliver_sent]; simp [hwv, (h2 q').2]
  · rw [deliver_recvd, deliver_sent]
    have := hle p
    by_cases hp : p = (v, q)
    · subst hp; rw [ite_eq_left rfl]; split_ifs <;> omega
    · rw [ite_eq_right hp]; split_ifs <;> omega

omit [Fintype V] in
/-- Starting the stage at a node gives a stage configuration. -/
lemma StageCfg.start {y : V → J} {σ : V → ℕ} {k : ℕ} {c : Config V P.State}
    (h : StageCfg P W y σ k c) {v : V} (hv : σ v < k) :
    StageCfg P W y (Function.update σ v k) k (startCfg P y v c) := by
  obtain ⟨⟨c', hr, hst, hrc, hs⟩, hun, hle⟩ := h
  refine ⟨⟨c', hr, hst, hrc, fun p => ?_⟩, fun w hw => ?_, fun p => ?_⟩
  · rw [hs]
    by_cases hp : p.1 = v
    · have := (hun v hv).2 p.2
      rw [show p = (v, p.2) from Prod.ext hp rfl] at this ⊢
      simp [startCfg, this.2, not_le.2 hv]
    · simp [startCfg, hp]
  · have hwv : w ≠ v := by rintro rfl; simp at hw
    rw [Function.update_of_ne hwv] at hw
    obtain ⟨h1, h2⟩ := hun w hw
    exact ⟨h1, fun q => ⟨(h2 q).1, by simp [startCfg, hwv, (h2 q).2]⟩⟩
  · have := hle p
    simp only [startCfg]; omega

/-- The decomposition of a configuration `c` of a staged execution: node `v` is in stage `σ v`
(`σ v = K`: halted), and `c` is the sum of one configuration `C k` per stage `k < K`. -/
structure Decomp (P : Proc J R) (dr : Driver I J R D) (W : Wiring V) (K : ℕ) (d : ℕ → V → D)
    (j : ℕ → V → J) (r : ℕ → V → R) (σ : V → ℕ) (C : ℕ → Config V P.State)
    (c : Config V (P.staged dr).State) : Prop where
  /-- Stages are at most `K`. -/
  le : ∀ v, σ v ≤ K
  /-- A running node is in its stage's configuration and has not returned from it. -/
  run : ∀ v, σ v < K → c.st v = (d (σ v) v, some ((C (σ v)).st v)) ∧
      P.result ((C (σ v)).st v) = none
  /-- A halted node is in its final driver state. -/
  halt : ∀ v, σ v = K → c.st v = (d K v, none)
  /-- Each stage configuration is a valid configuration of that stage. -/
  stage : ∀ k < K, StageCfg P W (j k) σ k (C k)
  /-- Nodes past stage `k` returned the scheduled result from it. -/
  res : ∀ k < K, ∀ v, k < σ v → P.result ((C k).st v) = some (r k v)
  /-- Sent pulses are the sum over the stages. -/
  sent : ∀ p, c.sent p = ∑ k ∈ range K, (C k).sent p
  /-- Received pulses are the sum over the stages. -/
  recvd : ∀ p, c.recvd p = ∑ k ∈ range K, (C k).recvd p

/-- The decomposition invariant of staged executions. -/
def StagedInv (P : Proc J R) (dr : Driver I J R D) (W : Wiring V) (K : ℕ) (d : ℕ → V → D)
    (j : ℕ → V → J) (r : ℕ → V → R) (c : Config V (P.staged dr).State) : Prop :=
  ∃ σ C, Decomp P dr W K d j r σ C c

omit [Encodable J] [Inhabited J] in
/-- Launching no stage halts. -/
lemma Proc.launch_none (P : Proc J R) (dd : D) : P.launch dd none = ((dd, none), fun _ => 0) := rfl
omit [Encodable J] [Inhabited J] in
/-- Launching a stage starts the procedure. -/
lemma Proc.launch_some (P : Proc J R) (dd : D) (a : J) :
    P.launch dd (some a) = ((dd, some (P.init a).1), (P.init a).2) := rfl

omit [Encodable I] [Inhabited I] in
/-- The decomposition invariant holds initially. -/
lemma stagedInv_init (hS : Schedule P dr W x K d j r) :
    StagedInv P dr W K d j r ((P.staged dr).initCfg x) := by
  refine ⟨fun _ => 0, fun k => if k = 0 then P.initCfg (j 0) else idleCfg P (j k), ?_⟩
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    refine ⟨fun _ => le_rfl, fun v h => absurd h (lt_irrefl _), fun v _ => ?_,
      fun k hk => absurd hk (Nat.not_lt_zero _), fun k hk => absurd hk (Nat.not_lt_zero _),
      fun p => ?_, fun p => ?_⟩
    · simp [Prog.initCfg, hS.start v, Proc.launch_none]
    · simp [Prog.initCfg, hS.start p.1, Proc.launch_none]
    · simp [Prog.initCfg]
  · refine ⟨fun _ => Nat.zero_le _, fun v _ => ?_, fun v h => absurd h hK.ne,
      fun k hk => ?_, fun k hk v h => absurd h (Nat.not_lt_zero _), fun p => ?_, fun p => ?_⟩
    · simp [Prog.initCfg, hS.start v, hK, Proc.launch_some, hS.init_none]
    · by_cases hk0 : k = 0
      · subst hk0
        refine ⟨⟨P.initCfg (j 0), Prog.Reach.init _, ?_, ?_, fun p => ?_⟩, fun v h => absurd h
          (Nat.not_lt_zero _), fun p => ?_⟩
        · simp
        · simp
        · simp
        · simp [Prog.initCfg]
      · refine ⟨⟨P.initCfg (j k), Prog.Reach.init _, ?_, ?_, fun p => ?_⟩, fun v _ => ?_,
          fun p => ?_⟩
        · funext v; simp [hk0, idleCfg, Prog.initCfg]
        · funext v; simp [hk0, idleCfg, Prog.initCfg]
        · simp [hk0, idleCfg, Prog.initCfg]
        · simp [hk0, idleCfg]
        · simp [hk0, idleCfg]
    · rw [sum_eq_single 0]
      · simp [Prog.initCfg, hS.start p.1, hK, Proc.launch_some]
      · intro b _ hb; simp [hb, idleCfg]
      · intro h; exact absurd (mem_range.2 hK) h
    · refine (sum_eq_zero fun k _ => ?_).symm
      split_ifs <;> rfl

omit [Encodable I] [Inhabited I] in
/-- **No mis-attributed pulses.** A node in stage `k` that can read a pulse in the staged
execution can read a pulse of stage `k`. -/
lemma Decomp.stage_avail (hS : Schedule P dr W x K d j r) {σ : V → ℕ} {C : ℕ → Config V P.State}
    {c : Config V (P.staged dr).State} (h : Decomp P dr W K d j r σ C c) {v : V} {q : Bool}
    (hvK : σ v < K) (hready : P.ready ((C (σ v)).st v) q = true)
    (havail : c.recvd (v, q) < c.sent (W.peer (v, q))) :
    (C (σ v)).recvd (v, q) < (C (σ v)).sent (W.peer (v, q)) := by
  obtain ⟨k, hk⟩ : ∃ k, σ v = k := ⟨_, rfl⟩
  rw [hk] at hvK hready ⊢
  set u := (W.peer (v, q)).1 with hu_def
  have hpe : W.peer (v, q) = (u, (W.peer (v, q)).2) := rfl
  by_cases hu : k < σ u
  · obtain ⟨⟨c', hr, hst, hrc, hs⟩, -, -⟩ := h.stage k hvK
    have hvn := (h.run v (hk ▸ hvK)).2
    rw [hk] at hvn
    have := (hS.comp k hvK).clean c' hr v q (by rw [hst]; exact hvn) (by rw [hst]; exact hready)
      (by rw [hst, ← hu_def, h.res k hvK u hu]; rfl)
    rw [hrc, hs, ← hu_def, ite_eq_left hu.le] at this
    simpa using this
  · push Not at hu
    have e1 : ∀ m ∈ (range K).erase k, (C m).recvd (v, q) = (C m).sent (W.peer (v, q)) := by
      intro m hm
      have hmk := ne_of_mem_erase hm
      have hmK := mem_range.1 (mem_of_mem_erase hm)
      rcases lt_or_gt_of_ne hmk with hlt | hgt
      · exact (h.stage m hmK).recvd_eq (hS.comp m hmK) (by rw [h.res m hmK v (by omega)]; rfl) q
      · have h1 := ((h.stage m hmK).2.1 v (by omega)).2 q
        have h2 := ((h.stage m hmK).2.1 u (by omega)).2 (W.peer (v, q)).2
        rw [h1.1, hpe, h2.2]
    rw [h.sent, h.recvd, ← add_sum_erase _ _ (mem_range.2 hvK),
      ← add_sum_erase _ _ (mem_range.2 hvK), sum_congr rfl e1] at havail
    omega

omit [Fintype V] [Encodable I] [Inhabited I] [Encodable J] [Inhabited J] in
/-- A reception that does not return stays in the stage. -/
lemma stagedRecv_of_none {dr : Driver I J R D} (dd : D) (s : P.State) (q : Bool)
    (h : P.result (P.recv s q).1 = none) :
    P.stagedRecv dr dd s q = ((dd, some (P.recv s q).1), (P.recv s q).2) := by
  simp [Proc.stagedRecv, h]

omit [Fintype V] [Encodable I] [Inhabited I] [Encodable J] [Inhabited J] in
/-- A reception that returns moves to the next stage. -/
lemma stagedRecv_of_some {dr : Driver I J R D} (dd : D) (s : P.State) (q : Bool) {rr : R}
    (h : P.result (P.recv s q).1 = some rr) :
    P.stagedRecv dr dd s q = ((P.launch (dr.next dd rr).1 (dr.next dd rr).2).1,
      fun p => (P.recv s q).2 p + (P.launch (dr.next dd rr).1 (dr.next dd rr).2).2 p) := by
  simp [Proc.stagedRecv, h]

/-- The decomposition invariant is preserved by every step of the staged program. -/
lemma stagedInv_step (hS : Schedule P dr W x K d j r) {c c' : Config V (P.staged dr).State}
    (hinv : StagedInv P dr W K d j r c) (hs : (P.staged dr).Step W c c') :
    StagedInv P dr W K d j r c' := by
  obtain ⟨σ, C, h⟩ := hinv
  obtain ⟨v, q, hterm, hready, havail⟩ := hs
  have hvK : σ v < K := by
    rcases lt_or_eq_of_le (h.le v) with hlt | heq
    · exact hlt
    · exfalso; rw [h.halt v heq] at hterm; simp at hterm
  obtain ⟨hcv, hnone⟩ := h.run v hvK
  have hready' : P.ready ((C (σ v)).st v) q = true := by
    have := hready; rw [hcv] at this; exact this
  have hA := h.stage_avail hS hvK hready' havail
  obtain ⟨k, hk⟩ : ∃ k, σ v = k := ⟨_, rfl⟩
  rw [hk] at hvK hcv hnone hready' hA
  set s := (C k).st v with hs_def
  set X := Cslib.ContentOblivious.deliver P.toAlgo (C k) v q with hX
  have hXst : (h.stage k hvK).deliver (v := v) (q := q) (by omega) hnone hready' hA =
    (h.stage k hvK).deliver (v := v) (q := q) (by omega) hnone hready' hA := rfl
  have hXcfg : StageCfg P W (j k) σ k X := (h.stage k hvK).deliver (by omega) hnone hready' hA
  have hXv : X.st v = (P.recv s q).1 := by simp [X, Cslib.ContentOblivious.deliver, s]
  have hXw : ∀ w, w ≠ v → X.st w = (C k).st w := fun w hw => deliver_st_ne _ _ _ _ hw
  have hXsent : ∀ p, X.sent p = (C k).sent p + if p.1 = v then (P.recv s q).2 p.2 else 0 :=
    fun p => deliver_sent _ _ _ p
  have hXrecvd : ∀ p, X.recvd p = (C k).recvd p + if p = (v, q) then 1 else 0 :=
    fun p => deliver_recvd _ _ _ p
  have hc'st : ∀ w, w ≠ v → (Cslib.ContentOblivious.deliver (P.staged dr).toAlgo c v q).st w =
      c.st w := fun w hw => deliver_st_ne _ _ _ _ hw
  have hrecv : (P.staged dr).toAlgo.recv (c.st v) q = P.stagedRecv dr (d k v) s q := by
    rw [hcv]
  rcases hres : P.result (P.recv s q).1 with _ | rr
  · -- the node stays in stage `k`
    have hsr := stagedRecv_of_none (dr := dr) (d k v) s q hres
    refine ⟨σ, fun m => if m = k then X else C m, ⟨h.le, fun w hw => ?_, fun w hw => ?_,
      fun m hm => ?_, fun m hm w hw => ?_, fun p => ?_, fun p => ?_⟩⟩
    · by_cases hwv : w = v
      · subst hwv
        rw [hk]
        simp only [ite_true]
        refine ⟨?_, by rw [hXv]; exact hres⟩
        rw [deliver_st_self, hrecv, hsr, hXv]
      · rw [hc'st w hwv, (h.run w hw).1]
        refine ⟨?_, ?_⟩
        · split_ifs with hwk
          · rw [hwk, hXw w hwv]
          · rfl
        · split_ifs with hwk
          · rw [hXw w hwv, ← hwk]; exact (h.run w hw).2
          · exact (h.run w hw).2
    · have hwv : w ≠ v := by rintro rfl; omega
      rw [hc'st w hwv, h.halt w hw]
    · split_ifs with hmk
      · subst hmk; exact hXcfg
      · exact h.stage m hm
    · split_ifs with hmk
      · subst hmk
        have hwv : w ≠ v := by rintro rfl; omega
        rw [hXw w hwv]; exact h.res m hm w hw
      · exact h.res m hm w hw
    · rw [deliver_sent, h.sent, hrecv, hsr]
      dsimp only
      have := sum_range_ite_eq hvK (fun m => (C m).sent p) (X.sent p)
      simp only at this
      have e : ∑ m ∈ range K, (if m = k then X else C m).sent p =
          ∑ m ∈ range K, if m = k then X.sent p else (C m).sent p :=
        sum_congr rfl fun m _ => by split_ifs <;> rfl
      rw [e, hXsent p] at *
      omega
    · rw [deliver_recvd, h.recvd]
      have := sum_range_ite_eq hvK (fun m => (C m).recvd p) (X.recvd p)
      simp only at this
      have e : ∑ m ∈ range K, (if m = k then X else C m).recvd p =
          ∑ m ∈ range K, if m = k then X.recvd p else (C m).recvd p :=
        sum_congr rfl fun m _ => by split_ifs <;> rfl
      rw [e, hXrecvd p] at *
      omega
  · -- the node returns `rr` from stage `k`
    have hrr : rr = r k v :=
      hXcfg.result_eq (hS.comp k hvK) (hS.ret k hvK) (by rw [hXv]; exact hres)
    subst hrr
    have hsr := stagedRecv_of_some (dr := dr) (d k v) s q hres
    rw [hS.next k hvK v] at hsr
    have hXret : P.result (X.st v) = some (r k v) := by rw [hXv]; exact hres
    let σ' := Function.update σ v (k + 1)
    have hσ'v : σ' v = k + 1 := by simp [σ']
    have hσ'w : ∀ w, w ≠ v → σ' w = σ w := fun w hw => by simp [σ', hw]
    have hcongr : ∀ m, m ≠ k + 1 → ∀ w, (m ≤ σ w ↔ m ≤ σ' w) := by
      intro m hm w
      by_cases hwv : w = v
      · subst hwv; rw [hσ'v, hk]; omega
      · rw [hσ'w w hwv]
    by_cases hK1 : k + 1 < K
    · -- start stage `k + 1`
      simp only [hK1, ite_true, Proc.launch_some] at hsr
      have hun := ((h.stage (k + 1) hK1).2.1 v (by omega))
      set Y := startCfg P (j (k + 1)) v (C (k + 1)) with hY
      have hYcfg : StageCfg P W (j (k + 1)) σ' (k + 1) Y := by
        exact (h.stage (k + 1) hK1).start (v := v) (by omega)
      refine ⟨σ', fun m => if m = k then X else if m = k + 1 then Y else C m,
        ⟨fun w => ?_, fun w hw => ?_, fun w hw => ?_, fun m hm => ?_, fun m hm w hw => ?_,
          fun p => ?_, fun p => ?_⟩⟩
      · by_cases hwv : w = v
        · subst hwv; rw [hσ'v]; omega
        · rw [hσ'w w hwv]; exact h.le w
      · by_cases hwv : w = v
        · subst hwv
          rw [hσ'v]
          simp only [show k + 1 ≠ k by omega, ite_false, ite_true]
          refine ⟨?_, ?_⟩
          · rw [deliver_st_self, hrecv, hsr]
            simp [Y, startCfg, hun.1]
          · simp [Y, startCfg, hun.1, hS.init_none]
        · rw [hσ'w w hwv] at hw ⊢
          rw [hc'st w hwv, (h.run w hw).1]
          refine ⟨?_, ?_⟩
          · split_ifs with h1 h2
            · rw [h1, hXw w hwv]
            · rw [h2]; rfl
            · rfl
          · split_ifs with h1 h2
            · rw [hXw w hwv, ← h1]; exact (h.run w hw).2
            · rw [show Y.st w = (C (k + 1)).st w from rfl, ← h2]; exact (h.run w hw).2
            · exact (h.run w hw).2
      · have hwv : w ≠ v := by rintro rfl; rw [hσ'v] at hw; omega
        rw [hσ'w w hwv] at hw
        rw [hc'st w hwv, h.halt w hw]
      · split_ifs with h1 h2
        · subst h1; exact hXcfg.congr (hcongr _ (by omega))
        · subst h2; exact hYcfg
        · exact (h.stage m hm).congr (hcongr m h2)
      · split_ifs with h1 h2
        · subst h1
          by_cases hwv : w = v
          · subst hwv; exact hXret
          · rw [hXw w hwv]; rw [hσ'w w hwv] at hw; exact h.res m hm w hw
        · subst h2
          have hwv : w ≠ v := by rintro rfl; rw [hσ'v] at hw; omega
          rw [hσ'w w hwv] at hw
          simp only [Y, startCfg]; exact h.res _ hm w hw
        · by_cases hwv : w = v
          · subst hwv; rw [hσ'v] at hw; exact h.res m hm w (by omega)
          · rw [hσ'w w hwv] at hw; exact h.res m hm w hw
      · rw [deliver_sent, h.sent, hrecv, hsr]
        dsimp only
        have h1 := sum_range_ite_eq hvK
          (fun m => if m = k + 1 then Y.sent p else (C m).sent p) (X.sent p)
        have h2 := sum_range_ite_eq hK1 (fun m => (C m).sent p) (Y.sent p)
        simp only [show k ≠ k + 1 by omega, ite_false] at h1 h2
        have e : ∑ m ∈ range K, (if m = k then X else if m = k + 1 then Y else C m).sent p =
            ∑ m ∈ range K, if m = k then X.sent p else
              (if m = k + 1 then Y.sent p else (C m).sent p) :=
          sum_congr rfl fun m _ => by split_ifs <;> rfl
        rw [e]
        have hYs : Y.sent p = (C (k + 1)).sent p +
            if p.1 = v then (P.init (j (k + 1) v)).2 p.2 else 0 := rfl
        have hXs := hXsent p
        by_cases hpv : p.1 = v
        · simp only [hpv, ite_true] at hXs hYs ⊢; omega
        · simp only [hpv, ite_false, add_zero] at hXs hYs ⊢; omega
      · rw [deliver_recvd, h.recvd]
        have h1 := sum_range_ite_eq hvK
          (fun m => if m = k + 1 then Y.recvd p else (C m).recvd p) (X.recvd p)
        have h2 := sum_range_ite_eq hK1 (fun m => (C m).recvd p) (Y.recvd p)
        simp only [show k ≠ k + 1 by omega, ite_false] at h1 h2
        have e : ∑ m ∈ range K, (if m = k then X else if m = k + 1 then Y else C m).recvd p =
            ∑ m ∈ range K, if m = k then X.recvd p else
              (if m = k + 1 then Y.recvd p else (C m).recvd p) :=
          sum_congr rfl fun m _ => by split_ifs <;> rfl
        rw [e]
        have hYr : Y.recvd p = (C (k + 1)).recvd p := rfl
        have hXr := hXrecvd p
        by_cases hpv : p = (v, q)
        · subst hpv; simp only [ite_true] at hXr ⊢; omega
        · simp only [hpv, ite_false, add_zero] at hXr ⊢; omega
    · -- halt
      have hKe : K = k + 1 := by omega
      simp only [hK1, ite_false, Proc.launch_none] at hsr
      refine ⟨σ', fun m => if m = k then X else C m,
        ⟨fun w => ?_, fun w hw => ?_, fun w hw => ?_, fun m hm => ?_, fun m hm w hw => ?_,
          fun p => ?_, fun p => ?_⟩⟩
      · by_cases hwv : w = v
        · subst hwv; rw [hσ'v]; omega
        · rw [hσ'w w hwv]; exact h.le w
      · have hwv : w ≠ v := by rintro rfl; rw [hσ'v] at hw; omega
        rw [hσ'w w hwv] at hw ⊢
        rw [hc'st w hwv, (h.run w hw).1]
        refine ⟨?_, ?_⟩
        · split_ifs with h1
          · rw [h1, hXw w hwv]
          · rfl
        · split_ifs with h1
          · rw [hXw w hwv, ← h1]; exact (h.run w hw).2
          · exact (h.run w hw).2
      · by_cases hwv : w = v
        · subst hwv
          rw [deliver_st_self, hrecv, hsr, hKe]
        · rw [hσ'w w hwv] at hw
          rw [hc'st w hwv, h.halt w hw]
      · split_ifs with h1
        · subst h1; exact hXcfg.congr (hcongr _ (by omega))
        · exact (h.stage m hm).congr (hcongr m (by omega))
      · split_ifs with h1
        · subst h1
          by_cases hwv : w = v
          · subst hwv; exact hXret
          · rw [hXw w hwv]; rw [hσ'w w hwv] at hw; exact h.res m hm w hw
        · by_cases hwv : w = v
          · subst hwv; rw [hσ'v] at hw; exact h.res m hm w (by omega)
          · rw [hσ'w w hwv] at hw; exact h.res m hm w hw
      · rw [deliver_sent, h.sent, hrecv, hsr]
        dsimp only
        have := sum_range_ite_eq hvK (fun m => (C m).sent p) (X.sent p)
        simp only at this
        have e : ∑ m ∈ range K, (if m = k then X else C m).sent p =
            ∑ m ∈ range K, if m = k then X.sent p else (C m).sent p :=
          sum_congr rfl fun m _ => by split_ifs <;> rfl
        rw [e, hXsent p] at *
        split_ifs at * <;> omega
      · rw [deliver_recvd, h.recvd]
        have := sum_range_ite_eq hvK (fun m => (C m).recvd p) (X.recvd p)
        simp only at this
        have e : ∑ m ∈ range K, (if m = k then X else C m).recvd p =
            ∑ m ∈ range K, if m = k then X.recvd p else (C m).recvd p :=
          sum_congr rfl fun m _ => by split_ifs <;> rfl
        rw [e, hXrecvd p] at *
        omega

/-- The decomposition invariant holds in every reachable configuration. -/
lemma stagedInv_reach (hS : Schedule P dr W x K d j r) {c : Config V (P.staged dr).State}
    (hc : (P.staged dr).Reach W x c) : StagedInv P dr W K d j r c :=
  Prog.Reach.induction (stagedInv_init hS) (fun _ _ _ hs ih => stagedInv_step hS ih hs) hc

omit [Fintype V] in
/-- A stage configuration that every node reached is reachable in the stage. -/
lemma StageCfg.eq_witness {y : V → J} {σ : V → ℕ} {k : ℕ} {c : Config V P.State}
    (h : StageCfg P W y σ k c) (hall : ∀ w, k ≤ σ w) : P.Reach W y c := by
  obtain ⟨⟨c', hr, hst, hrc, hs⟩, -, -⟩ := h
  have : c' = c := by
    ext
    · rw [hst]
    · rename_i p; rw [hs, ite_eq_left (hall p.1), add_zero]
    · rw [hrc]
  rwa [this] at hr

omit [Fintype V] in
/-- In a stage configuration, no more pulses are received than sent. -/
lemma StageCfg.recvd_le_sent {y : V → J} {σ : V → ℕ} {k : ℕ} {c : Config V P.State}
    (h : StageCfg P W y σ k c) (p : V × Bool) : c.recvd p ≤ c.sent (W.peer p) := h.2.2 p

/-- In a final configuration of the staged program every node has halted. -/
lemma Decomp.all_halted (hS : Schedule P dr W x K d j r) {σ : V → ℕ} {C : ℕ → Config V P.State}
    {c : Config V (P.staged dr).State} (h : Decomp P dr W K d j r σ C c)
    (hfin : (P.staged dr).Final W c) : ∀ v, σ v = K := by
  by_contra hne
  push Not at hne
  obtain ⟨v0, hv0⟩ := hne
  have hlt0 : σ v0 < K := lt_of_le_of_ne (h.le v0) hv0
  obtain ⟨vm, -, hvm⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) ⟨v0, mem_univ v0⟩ σ
  have hmin : ∀ w, σ vm ≤ σ w := fun w => hvm ▸ Finset.inf'_le _ (mem_univ w)
  obtain ⟨k, hk⟩ : ∃ k, σ vm = k := ⟨_, rfl⟩
  rw [hk] at hmin
  have hkK : k < K := lt_of_le_of_lt (hmin v0) hlt0
  have hvmK : σ vm < K := hk ▸ hkK
  have hrk := (h.stage k hkK).eq_witness hmin
  have hnf : ¬ P.Final W (C k) := by
    intro hF
    have := ((hS.comp k hkK).final (C k) hrk hF).2 vm
    have h2 := (h.run vm hvmK).2
    rw [hk] at h2
    rw [h2] at this; simp at this
  simp only [Prog.Final, Cslib.ContentOblivious.Final, not_forall, not_not] at hnf
  obtain ⟨w, q, hterm, hready, havail⟩ := hnf
  have hwk : σ w = k := by
    by_contra hne
    have := h.res k hkK w (lt_of_le_of_ne (hmin w) (Ne.symm hne))
    simp only [P.terminated_eq, this] at hterm
    simp at hterm
  have hwK : σ w < K := hwk ▸ hkK
  have hcw := (h.run w hwK).1
  rw [hwk] at hcw
  apply hfin w q
  refine ⟨?_, ?_, ?_⟩
  · simp [hcw]
  · simpa [hcw] using hready
  · rw [h.sent, h.recvd]
    exact Finset.sum_lt_sum (fun m hm => (h.stage m (mem_range.1 hm)).recvd_le_sent (w, q))
      ⟨k, mem_range.2 hkK, havail⟩

omit [Encodable I] [Inhabited I] in
/-- Every pulse count of a staged execution is the sum of the pulse counts of its stages. -/
lemma Decomp.totalSent_le {σ : V → ℕ}
    {C : ℕ → Config V P.State} {c : Config V (P.staged dr).State}
    (h : Decomp P dr W K d j r σ C c) {B : ℕ → ℕ}
    (hB : ∀ k < K, ∀ c, P.Reach W (j k) c → totalSent c ≤ B k) :
    totalSent c ≤ ∑ k ∈ range K, B k := by
  have e : totalSent c = ∑ k ∈ range K, totalSent (C k) := by
    unfold totalSent
    simp_rw [h.sent]
    exact Finset.sum_comm
  rw [e]
  refine Finset.sum_le_sum fun k hk => ?_
  obtain ⟨⟨c', hr, -, -, hs⟩, -, -⟩ := h.stage k (mem_range.1 hk)
  refine le_trans (Finset.sum_le_sum fun p _ => ?_) (hB k (mem_range.1 hk) c' hr)
  rw [hs]; exact Nat.le_add_right _ _

/-- **Staged executions (Theorem 9, generalized).** If all stages are composable and return the
scheduled results, every final configuration of the staged program is quiescent and every node
has halted in its scheduled final local state. -/
theorem Schedule.final (hS : Schedule P dr W x K d j r) {c : Config V (P.staged dr).State}
    (hc : (P.staged dr).Reach W x c) (hfin : (P.staged dr).Final W c) :
    (P.staged dr).Quiescent W c ∧ ∀ v, c.st v = (d K v, none) := by
  obtain ⟨σ, C, h⟩ := stagedInv_reach hS hc
  have hall := h.all_halted hS hfin
  refine ⟨fun p => ?_, fun v => h.halt v (hall v)⟩
  rw [h.sent, h.recvd]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmK := mem_range.1 hm
  have := (h.stage m hmK).recvd_eq (hS.comp m hmK)
    (v := p.1) (by rw [h.res m hmK p.1 (by rw [hall]; exact hmK)]; rfl) p.2
  simpa using this

/-- Pulse complexity of staged executions: at most the sum of the per-stage bounds. -/
theorem Schedule.totalSent_le (hS : Schedule P dr W x K d j r) {B : ℕ → ℕ}
    (hB : ∀ k < K, ∀ c, P.Reach W (j k) c → totalSent c ≤ B k)
    {c : Config V (P.staged dr).State} (hc : (P.staged dr).Reach W x c) :
    totalSent c ≤ ∑ k ∈ range K, B k := by
  obtain ⟨σ, C, h⟩ := stagedInv_reach hS hc
  exact h.totalSent_le hB

/-- The staged program returns the scheduled final local states. -/
theorem Schedule.returns (hS : Schedule P dr W x K d j r) :
    (P.staged dr).Returns W x (d K) := by
  intro c hc hfin v
  rw [(hS.final hc hfin).2 v]

/-- A staged program whose stages are composable is itself composable: it can in turn be used
as a stage (nested composition). -/
theorem Schedule.composable (hS : Schedule P dr W x K d j r) {B : ℕ → ℕ}
    (hB : ∀ k < K, ∀ c, P.Reach W (j k) c → totalSent c ≤ B k) :
    (P.staged dr).Composable W x where
  bounded := ⟨_, fun c hc => hS.totalSent_le hB hc⟩
  final c hc hfin := ⟨(hS.final hc hfin).1, fun v => by rw [(hS.final hc hfin).2 v]; rfl⟩
  clean c hc v q hv hready hu := by
    obtain ⟨σ, C, h⟩ := stagedInv_reach hS hc
    set u := (W.peer (v, q)).1 with hu_def
    have hvK : σ v < K := by
      rcases lt_or_eq_of_le (h.le v) with hlt | heq
      · exact hlt
      · rw [h.halt v heq] at hv; simp at hv
    have huK : σ u = K := by
      rcases lt_or_eq_of_le (h.le u) with hlt | heq
      · rw [(h.run u hlt).1] at hu; simp at hu
      · exact heq
    obtain ⟨k, hk⟩ : ∃ k, σ v = k := ⟨_, rfl⟩
    have hcv := (h.run v hvK).1
    have hnone := (h.run v hvK).2
    rw [hk] at hcv hnone hvK
    have hready' : P.ready ((C k).st v) q = true := by rw [hcv] at hready; simpa using hready
    have hstrict : (C k).recvd (v, q) < (C k).sent (W.peer (v, q)) := by
      obtain ⟨⟨c', hr, hst, hrc, hs⟩, -, -⟩ := h.stage k hvK
      have := (hS.comp k hvK).clean c' hr v q (by rw [hst]; exact hnone)
        (by rw [hst]; exact hready')
        (by rw [hst, ← hu_def, h.res k hvK u (by omega)]; rfl)
      rw [hrc, hs, ← hu_def, ite_eq_left (by omega)] at this
      simpa using this
    rw [h.sent, h.recvd]
    exact Finset.sum_lt_sum (fun m hm => (h.stage m (mem_range.1 hm)).recvd_le_sent (v, q))
      ⟨k, mem_range.2 hvK, hstrict⟩

end staged

/-! ## Schedules from synchronous runs

Instead of guessing the schedule of a staged program, one can compute it: run the driver of
every node synchronously, stage by stage, using an *oracle* `F` for the results of each stage
(`F j v`: what node `v` returns when the stage runs with inputs `j`). If all nodes leave the loop
in the same stage and every stage is composable and returns what the oracle says, the synchronous
run is a schedule (`schedule_of_syncRun`). -/

section syncRun

variable [Fintype V] {I J R D : Type} [Encodable I] [Inhabited I] [Encodable J] [Inhabited J]

/-- The synchronous run of a driver with stage results given by the oracle `F`: the local state
and pending stage input of every node before stage `k`. -/
def syncRun (dr : Driver I J R D) (F : (V → J) → V → R) (x : V → I) : ℕ → V → D × Option J
  | 0 => fun v => dr.start (x v)
  | k + 1 => fun v => match (syncRun dr F x k v).2 with
    | none => syncRun dr F x k v
    | some _ => dr.next (syncRun dr F x k v).1
        (F (fun w => ((syncRun dr F x k w).2).getD default) v)

/-- The stage inputs of the synchronous run. -/
def syncInput (dr : Driver I J R D) (F : (V → J) → V → R) (x : V → I) (k : ℕ) (v : V) : J :=
  ((syncRun dr F x k v).2).getD default

omit [DecidableEq V] [Fintype V] [Encodable I] [Inhabited I] [Encodable J] in
/-- The synchronous run takes one driver step at a running node. -/
lemma syncRun_succ (dr : Driver I J R D) (F : (V → J) → V → R) (x : V → I) {k : ℕ} {v : V}
    (h : ((syncRun dr F x k v).2).isSome) :
    syncRun dr F x (k + 1) v = dr.next (syncRun dr F x k v).1 (F (syncInput dr F x k) v) := by
  change (match (syncRun dr F x k v).2 with
    | none => syncRun dr F x k v
    | some _ => dr.next (syncRun dr F x k v).1
        (F (fun w => ((syncRun dr F x k w).2).getD default) v)) = _
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h
  rw [ha]; rfl

omit [Encodable I] [Inhabited I] in
/-- **A synchronous run is a schedule.** -/
theorem schedule_of_syncRun {P : Proc J R} {dr : Driver I J R D} {W : Wiring V}
    {F : (V → J) → V → R} {x : V → I} (K : ℕ)
    (hinit : ∀ a, P.result (P.init a).1 = none)
    (hrun : ∀ k < K, ∀ v, ((syncRun dr F x k v).2).isSome)
    (hhalt : ∀ v, (syncRun dr F x K v).2 = none)
    (hcomp : ∀ k < K, P.Composable W (syncInput dr F x k))
    (hret : ∀ k < K, P.Returns W (syncInput dr F x k) (F (syncInput dr F x k))) :
    Schedule P dr W x K (fun k v => (syncRun dr F x k v).1) (syncInput dr F x)
      (fun k => F (syncInput dr F x k)) := by
  have hsome : ∀ k < K, ∀ v, (syncRun dr F x k v).2 = some (syncInput dr F x k v) := by
    intro k hk v
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (hrun k hk v)
    simp [syncInput, ha]
  refine ⟨hinit, fun v => ?_, fun k hk v => ?_, hcomp, hret⟩
  · have e : dr.start (x v) = syncRun dr F x 0 v := rfl
    rw [e]
    refine Prod.ext rfl ?_
    split_ifs with h
    · exact hsome 0 h v
    · have : K = 0 := by omega
      subst this; exact hhalt v
  · rw [← syncRun_succ dr F x (hrun k hk v)]
    refine Prod.ext rfl ?_
    split_ifs with h
    · exact hsome _ h v
    · have : k + 1 = K := by omega
      rw [this]; exact hhalt v

end syncRun

end Cslib.ContentOblivious
