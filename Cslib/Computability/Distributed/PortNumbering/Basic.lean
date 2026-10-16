/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Anonymous port-numbered networks

The *port-numbering model* of distributed computing (Angluin 1980; see e.g. Suomela, *Distributed
algorithms for edge dominating sets*, PODC 2010, §2): anonymous nodes, deterministic synchronous
rounds, and every node distinguishes its incident edges only by local port numbers.

## Main definitions

* `PNGraph V`: a port-numbered (multi)graph on the node set `V`. Node `v` has `deg v` ports,
  numbered `0, …, deg v - 1` (papers usually use `1, …, d`); `p v i = (u, j)` says that port `i` of
  `v` is connected to port `j` of `u`. `p` is an involution on the set of ports. Loops,
  half-loops (fixed points of `p`) and parallel edges are allowed (they are needed for the
  quotient graphs of covering-map lower bounds); `IsSimple` singles out simple graphs, and
  `toSimpleGraph` is the underlying `SimpleGraph`.
* `Algorithm I O`: a deterministic synchronous message-passing algorithm with local inputs in `I`
  and local outputs in `O`. Initially a node knows only its degree and its local input. In each
  round every node sends one message to each of its ports (the message may depend on the port
  number), receives one message from each port (indexed by its own port number, `none` for
  non-existing ports), and updates its state. There are no identifiers, no randomness; states and
  messages are unbounded. A `T`-round run of `A` on `G` with input `x` has output
  `A.eval G T x : V → O`.
* `PNGraph.IsCovering G H f`: a covering map (degree- and connection-preserving map).
* Composition: `Algorithm.seq A T₁ B` (run `A` for `T₁` rounds, then `B` on `A`'s outputs), and
  **local processes** `Algorithm.ofLocal L` (in round `r` every node replaces its local data by
  `L r deg data inbox`, where `inbox i = (neighbour's data, neighbour's port)`). The latter is the
  convenient way to write algorithms: reason about `localRun`, a synchronous update of the whole
  configuration, and get a genuine message-passing algorithm for free.

## Main results

* `Algorithm.state_covering`: a node and its image under a covering map run through identical
  states (the standard lower-bound argument).
* `Algorithm.eval_seq`: semantics of sequential composition.
* `Algorithm.eval_ofLocal`: the run of `ofLocal L` is the global iteration `localRun`.

## References

* D. Angluin, *Local and global properties in networks of processors*, STOC 1980.
* J. Suomela, *Distributed algorithms for edge dominating sets*, PODC 2010.
-/

@[expose] public section

namespace Cslib.PortNumbering

/-- A port-numbered graph: node `v` has ports `0, …, deg v - 1`, and port `i` of `v` is connected
to port `(p v i).2` of node `(p v i).1`. The connection map `p` is an involution on ports. (Values
of `p v i` for `i ≥ deg v` are irrelevant.) -/
structure PNGraph (V : Type*) where
  /-- The degree (number of ports) of a node. -/
  deg : V → ℕ
  /-- `p v i = (u, j)`: port `i` of `v` is connected to port `j` of `u`. -/
  p : V → ℕ → V × ℕ
  p_lt : ∀ v i, i < deg v → (p v i).2 < deg (p v i).1
  p_p : ∀ v i, i < deg v → p (p v i).1 (p v i).2 = (v, i)

namespace PNGraph

variable {V W : Type*} (G : PNGraph V)

/-- The neighbour behind port `i` of `v`. -/
def nbr (v : V) (i : ℕ) : V := (G.p v i).1

/-- The port number at the other end of port `i` of `v`. -/
def rport (v : V) (i : ℕ) : ℕ := (G.p v i).2

theorem p_eq (v : V) (i : ℕ) : G.p v i = (G.nbr v i, G.rport v i) := rfl

theorem rport_lt {v : V} {i : ℕ} (h : i < G.deg v) : G.rport v i < G.deg (G.nbr v i) :=
  G.p_lt v i h

@[simp] theorem nbr_nbr {v : V} {i : ℕ} (h : i < G.deg v) :
    G.nbr (G.nbr v i) (G.rport v i) = v := by
  have := G.p_p v i h; simp only [nbr, rport] at *; rw [this]

@[simp] theorem rport_rport {v : V} {i : ℕ} (h : i < G.deg v) :
    G.rport (G.nbr v i) (G.rport v i) = i := by
  have := G.p_p v i h; simp only [nbr, rport] at *; rw [this]

/-- A port-numbered graph is *simple* if it has no loops and no parallel edges: the neighbours
behind different ports of a node are different, and different from the node itself. -/
def IsSimple : Prop :=
  (∀ v i, i < G.deg v → G.nbr v i ≠ v) ∧
    ∀ v i j, i < G.deg v → j < G.deg v → G.nbr v i = G.nbr v j → i = j

/-- The underlying simple graph: `u ~ v` iff `u ≠ v` and some port of `u` leads to `v`. -/
def toSimpleGraph : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ i < G.deg u, G.nbr u i = v
  symm := ⟨by
    rintro u v ⟨hne, i, hi, rfl⟩
    exact ⟨hne.symm, G.rport u i, G.rport_lt hi, G.nbr_nbr hi⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem toSimpleGraph_adj {u v : V} :
    G.toSimpleGraph.Adj u v ↔ u ≠ v ∧ ∃ i < G.deg u, G.nbr u i = v := Iff.rfl

theorem adj_nbr (hG : G.IsSimple) {v : V} {i : ℕ} (hi : i < G.deg v) :
    G.toSimpleGraph.Adj v (G.nbr v i) := ⟨(hG.1 v i hi).symm, i, hi, rfl⟩

/-- In a simple graph, the port leading to a given neighbour is unique. -/
theorem port_unique (hG : G.IsSimple) {v : V} {i j : ℕ} (hi : i < G.deg v) (hj : j < G.deg v)
    (h : G.nbr v i = G.nbr v j) : i = j := hG.2 v i j hi hj h

/-- The edge behind port `i` of `v`. -/
def edge (v : V) (i : ℕ) : Sym2 V := s(v, G.nbr v i)

theorem edge_nbr {v : V} {i : ℕ} (h : i < G.deg v) :
    G.edge (G.nbr v i) (G.rport v i) = G.edge v i := by
  simp [edge, G.nbr_nbr h, Sym2.eq_swap]

theorem edge_mem_edgeSet (hG : G.IsSimple) {v : V} {i : ℕ} (hi : i < G.deg v) :
    G.edge v i ∈ G.toSimpleGraph.edgeSet := G.adj_nbr hG hi

/-- In a simple port-numbered graph every edge of the underlying graph is the edge behind some
port. -/
theorem exists_port_of_adj {u v : V} (h : G.toSimpleGraph.Adj u v) :
    ∃ i < G.deg u, G.nbr u i = v := h.2

/-- In a simple graph the degree in the underlying simple graph is the port degree. -/
theorem degree_eq [Fintype V] [DecidableRel G.toSimpleGraph.Adj]
    (hG : G.IsSimple) (v : V) : G.toSimpleGraph.degree v = G.deg v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : G.toSimpleGraph.neighborFinset v = (Finset.range (G.deg v)).image (G.nbr v) := by
    ext u
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨-, i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact G.adj_nbr hG hi
  rw [this, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj h
  exact hG.2 v i j (by simpa using hi) (by simpa using hj) h

/-! ### Covering maps -/

/-- `f : V → W` is a covering map from `G` to `H` (§2.3 of Suomela, PODC'10): it preserves
degrees and connections. (Surjectivity, required in the paper, is irrelevant for the lifting
argument and omitted.) -/
structure IsCovering (G : PNGraph V) (H : PNGraph W) (f : V → W) : Prop where
  deg_eq : ∀ v, H.deg (f v) = G.deg v
  p_eq : ∀ v i, i < G.deg v → H.p (f v) i = (f (G.nbr v i), G.rport v i)

end PNGraph

/-! ### Algorithms -/

/-- A deterministic synchronous algorithm in the port-numbering model with local inputs `I` and
local outputs `O`. Initially a node knows its degree and its local input. In each round a node in
state `s` sends `send s i` to its port `i` and then moves to `recv s m`, where `m i` is the
message received from port `i` (`none` if `i ≥ deg`). The output after the last round is `out s`. -/
structure Algorithm (I O : Type) where
  /-- Local states. -/
  State : Type
  /-- Messages. -/
  Msg : Type
  /-- Initial state from the degree and the local input. -/
  init : ℕ → I → State
  /-- The message sent to port `i`. -/
  send : State → ℕ → Msg
  /-- State transition on receiving messages (indexed by own port numbers). -/
  recv : State → (ℕ → Option Msg) → State
  /-- Local output. -/
  out : State → O

namespace Algorithm

variable {I J O : Type} {V W : Type*}

/-- The messages received by `v` when the nodes are in states `s`. -/
def inbox (A : Algorithm I O) (G : PNGraph V) (s : V → A.State) (v : V) : ℕ → Option A.Msg :=
  fun i => if i < G.deg v then some (A.send (s (G.nbr v i)) (G.rport v i)) else none

/-- The state of every node after `t` rounds of `A` on `G` with local inputs `x`. -/
def state (A : Algorithm I O) (G : PNGraph V) (x : V → I) : ℕ → V → A.State
  | 0 => fun v => A.init (G.deg v) (x v)
  | t + 1 => fun v => A.recv (A.state G x t v) (A.inbox G (A.state G x t) v)

/-- The local outputs after running `A` for `T` rounds on `G` with local inputs `x`. -/
def eval (A : Algorithm I O) (G : PNGraph V) (T : ℕ) (x : V → I) : V → O :=
  fun v => A.out (A.state G x T v)

@[simp] theorem state_zero (A : Algorithm I O) (G : PNGraph V) (x : V → I) (v : V) :
    A.state G x 0 v = A.init (G.deg v) (x v) := rfl

theorem state_succ (A : Algorithm I O) (G : PNGraph V) (x : V → I) (t : ℕ) (v : V) :
    A.state G x (t + 1) v = A.recv (A.state G x t v) (A.inbox G (A.state G x t) v) := rfl

/-- **Covering maps preserve runs**: if `f` is a covering map from `G` to `H` and the inputs are
pulled back along `f`, then every node of `G` is in the same state as its image in `H`, in every
round. Hence any deterministic algorithm produces the same output at `v` and `f v`. -/
theorem state_covering (A : Algorithm I O) {G : PNGraph V} {H : PNGraph W} {f : V → W}
    (hf : G.IsCovering H f) (x : W → I) (t : ℕ) (v : V) :
    A.state G (x ∘ f) t v = A.state H x t (f v) := by
  induction t generalizing v with
  | zero => simp [hf.deg_eq]
  | succ t ih =>
    rw [state_succ, state_succ, ih]
    congr 1
    funext i
    simp only [inbox, hf.deg_eq]
    split_ifs with hi
    · have := hf.p_eq v i hi
      simp only [PNGraph.nbr, PNGraph.rport] at this ⊢
      rw [ih, this]
    · rfl

theorem eval_covering (A : Algorithm I O) {G : PNGraph V} {H : PNGraph W} {f : V → W}
    (hf : G.IsCovering H f) (T : ℕ) (x : W → I) (v : V) :
    A.eval G T (x ∘ f) v = A.eval H T x (f v) := by
  simp [eval, state_covering A hf]

/-! ### Sequential composition -/

/-- Normalisation used by `seq`: after `T₁` rounds switch from `A` to `B`. -/
def seqNorm (A : Algorithm I J) (T₁ : ℕ) (B : Algorithm J O) :
    ℕ × ℕ × (A.State ⊕ B.State) → ℕ × ℕ × (A.State ⊕ B.State)
  | (d, r, .inl s) => if r = T₁ then (d, r, .inr (B.init d (A.out s))) else (d, r, .inl s)
  | (d, r, .inr s) => (d, r, .inr s)

/-- `A.seq T₁ B`: run `A` for `T₁` rounds, then run `B` with `A`'s outputs as local inputs. The
state records the degree and the number of rounds so far. -/
def seq (A : Algorithm I J) (T₁ : ℕ) (B : Algorithm J O) : Algorithm I O where
  State := ℕ × ℕ × (A.State ⊕ B.State)
  Msg := A.Msg ⊕ B.Msg
  init d x := seqNorm A T₁ B (d, 0, .inl (A.init d x))
  send
    | (_, _, .inl s), i => .inl (A.send s i)
    | (_, _, .inr s), i => .inr (B.send s i)
  recv
    | (d, r, .inl s), m =>
      seqNorm A T₁ B (d, r + 1, .inl (A.recv s fun i => (m i).bind Sum.getLeft?))
    | (d, r, .inr s), m => (d, r + 1, .inr (B.recv s fun i => (m i).bind Sum.getRight?))
  out
    | (d, _, .inl s) => B.out (B.init d (A.out s))
    | (_, _, .inr s) => B.out s

section seqLemmas
variable (A : Algorithm I J) (T₁ : ℕ) (B : Algorithm J O)
@[simp] theorem seq_send_inl (d r : ℕ) (s : A.State) (i : ℕ) :
    (A.seq T₁ B).send (d, r, .inl s) i = .inl (A.send s i) := rfl
@[simp] theorem seq_send_inr (d r : ℕ) (s : B.State) (i : ℕ) :
    (A.seq T₁ B).send (d, r, .inr s) i = .inr (B.send s i) := rfl
theorem seq_recv_inl (d r : ℕ) (s : A.State) (m) :
    (A.seq T₁ B).recv (d, r, .inl s) m =
      seqNorm A T₁ B (d, r + 1, .inl (A.recv s fun i => (m i).bind Sum.getLeft?)) := rfl
theorem seq_recv_inr (d r : ℕ) (s : B.State) (m) :
    (A.seq T₁ B).recv (d, r, .inr s) m =
      (d, r + 1, .inr (B.recv s fun i => (m i).bind Sum.getRight?)) := rfl
theorem seq_init (d : ℕ) (x : I) :
    (A.seq T₁ B).init d x = seqNorm A T₁ B (d, 0, .inl (A.init d x)) := rfl
@[simp] theorem seq_out_inr (d r : ℕ) (s : B.State) : (A.seq T₁ B).out (d, r, .inr s) = B.out s :=
  rfl
end seqLemmas

theorem inbox_seq_inl (A : Algorithm I J) (T₁ : ℕ) (B : Algorithm J O) (G : PNGraph V)
    (s : V → (A.seq T₁ B).State) (s' : V → A.State)
    (hs : ∀ u, ∃ d r, s u = (d, r, .inl (s' u))) (v : V) :
    (fun i => ((A.seq T₁ B).inbox G s v i).bind Sum.getLeft?) = A.inbox G s' v := by
  funext i
  unfold inbox
  split_ifs
  · obtain ⟨d, r, h⟩ := hs (G.nbr v i); rw [h]; rfl
  · rfl

theorem inbox_seq_inr (A : Algorithm I J) (T₁ : ℕ) (B : Algorithm J O) (G : PNGraph V)
    (s : V → (A.seq T₁ B).State) (s' : V → B.State)
    (hs : ∀ u, ∃ d r, s u = (d, r, .inr (s' u))) (v : V) :
    (fun i => ((A.seq T₁ B).inbox G s v i).bind Sum.getRight?) = B.inbox G s' v := by
  funext i
  unfold inbox
  split_ifs
  · obtain ⟨d, r, h⟩ := hs (G.nbr v i); rw [h]; rfl
  · rfl

theorem state_seq_lt (A : Algorithm I J) (T₁ : ℕ) (B : Algorithm J O) (G : PNGraph V)
    (x : V → I) {t : ℕ} (ht : t < T₁) (v : V) :
    (A.seq T₁ B).state G x t v = (G.deg v, t, .inl (A.state G x t v)) := by
  induction t generalizing v with
  | zero => simp only [state_zero, seq_init, seqNorm, ht.ne, ite_false]; rfl
  | succ t ih =>
    rw [state_succ, ih (by omega), seq_recv_inl,
      inbox_seq_inl A T₁ B G _ _ (fun u => ⟨_, _, ih (by omega) u⟩)]
    simp only [seqNorm, (show t + 1 ≠ T₁ by omega), ite_false, state_succ]; rfl

theorem state_seq_ge (A : Algorithm I J) (T₁ : ℕ) (B : Algorithm J O) (G : PNGraph V)
    (x : V → I) (t : ℕ) (v : V) :
    (A.seq T₁ B).state G x (T₁ + t) v =
      (G.deg v, T₁ + t, .inr (B.state G (A.eval G T₁ x) t v)) := by
  induction t generalizing v with
  | zero =>
    rcases Nat.eq_zero_or_pos T₁ with h | h
    · subst h; simp only [Nat.add_zero, state_zero, seq_init, seqNorm, ite_true]; rfl
    · obtain ⟨T, rfl⟩ : ∃ T, T₁ = T + 1 := ⟨T₁ - 1, by omega⟩
      rw [Nat.add_zero, state_succ, state_seq_lt A _ B G x (by omega), seq_recv_inl,
        inbox_seq_inl A _ B G _ _ (fun u => ⟨_, _, state_seq_lt A _ B G x (by omega) u⟩)]
      simp only [seqNorm, ite_true, state_zero, eval, state_succ]; rfl
  | succ t ih =>
    rw [← Nat.add_assoc, state_succ, ih, seq_recv_inr, state_succ,
      inbox_seq_inr A T₁ B G _ _ (fun u => ⟨_, _, ih u⟩)]

/-- Semantics of sequential composition. -/
theorem eval_seq (A : Algorithm I J) (T₁ : ℕ) (B : Algorithm J O) (G : PNGraph V)
    (T₂ : ℕ) (x : V → I) :
    (A.seq T₁ B).eval G (T₁ + T₂) x = B.eval G T₂ (A.eval G T₁ x) := by
  funext v
  simp only [eval, state_seq_ge, seq_out_inr]

/-! ### Local processes -/

/-- The information a node receives in one full-information round when the configuration is
`x`: for each port `i < deg v`, the neighbour's local data and the neighbour's port number. -/
def nbrInfo {J : Type} (G : PNGraph V) (x : V → J) (v : V) : ℕ → Option (J × ℕ) :=
  fun i => if i < G.deg v then some (x (G.nbr v i), G.rport v i) else none

/-- A synchronous local process: in round `r` (counting from `0`) every node `v` replaces its local
data `x v` by `L r (deg v) (x v) (nbrInfo x v)`. -/
def localRun {J : Type} (G : PNGraph V) (L : ℕ → ℕ → J → (ℕ → Option (J × ℕ)) → J)
    (x : V → J) : ℕ → V → J
  | 0 => x
  | r + 1 => fun v => L r (G.deg v) (localRun G L x r v) (nbrInfo G (localRun G L x r) v)

@[simp] theorem localRun_zero {J : Type} (G : PNGraph V) (L) (x : V → J) :
    localRun G L x 0 = x := rfl

theorem localRun_succ {J : Type} (G : PNGraph V) (L) (x : V → J) (r : ℕ) (v : V) :
    localRun G L x (r + 1) v =
      L r (G.deg v) (localRun G L x r v) (nbrInfo G (localRun G L x r) v) := rfl

/-- The message-passing algorithm implementing a local process: full-information messages
(local data plus the port number it is sent to), plus a round counter. -/
def ofLocal {J : Type} (L : ℕ → ℕ → J → (ℕ → Option (J × ℕ)) → J) : Algorithm J J where
  State := ℕ × ℕ × J
  Msg := J × ℕ
  init d x := (d, 0, x)
  send s i := (s.2.2, i)
  recv s m := (s.1, s.2.1 + 1, L s.2.1 s.1 s.2.2 m)
  out s := s.2.2

theorem state_ofLocal {J : Type} (L : ℕ → ℕ → J → (ℕ → Option (J × ℕ)) → J) (G : PNGraph V)
    (x : V → J) (t : ℕ) (v : V) :
    (ofLocal L).state G x t v = (G.deg v, t, localRun G L x t v) := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    rw [state_succ, ih, localRun_succ]
    change (_, _, _) = _
    congr 2
    change L t (G.deg v) _ _ = _
    congr 1
    funext i
    simp only [inbox, nbrInfo]
    split_ifs
    · rw [ih]; rfl
    · rfl

/-- A `T`-round run of the algorithm `ofLocal L` computes `localRun G L x T`. -/
theorem eval_ofLocal {J : Type} (L : ℕ → ℕ → J → (ℕ → Option (J × ℕ)) → J) (G : PNGraph V)
    (T : ℕ) (x : V → J) : (ofLocal L).eval G T x = localRun G L x T := by
  funext v; simp only [eval, state_ofLocal]; rfl

/-- A `0`-round algorithm computing `f deg input` locally. -/
def ofFun (f : ℕ → I → O) : Algorithm I O where
  State := ℕ × I
  Msg := Unit
  init d x := (d, x)
  send _ _ := ()
  recv s _ := s
  out s := f s.1 s.2

theorem eval_ofFun (f : ℕ → I → O) (G : PNGraph V) (x : V → I) (v : V) :
    (ofFun f).eval G 0 x v = f (G.deg v) (x v) := rfl

end Algorithm

end Cslib.PortNumbering
