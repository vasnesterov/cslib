/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.MessagePassing.Bits

/-! # Protocols run by a subset of the processes

Protocols for *committees* (subsets of the processes) are written over a type `Q` of their own
processes, typically the subtype `↥X` of a committee `X : Finset P`, so that everything proved
about protocols over an arbitrary process type applies to them verbatim (with the committee size
as the number of processes). Such a protocol is run inside a protocol over `P` along an embedding
`e : SubProcesses Q P` of `Q` into `P` with a partial inverse: in `A.embed e`, the members (the
processes `e.emb q`) run `A`, messages from non-members are dropped, and non-members are inert
(they produce no outputs). Embedded protocols are typically children of a composite
(`Cslib.Distributed.Protocol.compose`).

A run `ρ` of `A.embed e` restricts to a run `ρ.restrict e` of `A`: its faulty processes are the
members that are faulty in `ρ`, and its clocks and inputs are those of the members (messages from
non-members removed).

## Main definitions

* `SubProcesses Q P`: an embedding of `Q` into `P` with a partial inverse; `SubProcesses.ofFinset`
  (a committee `↥X` inside `P`), `SubProcesses.ofSubset` (a committee `↥X` inside a committee
  `↥C ⊇ ↥X`), `SubProcesses.trans` (composition); `SubProcesses.members` (the members, as a set of
  processes of `P`); `SubProcesses.preimage` (the members in a set of processes, e.g. the faulty
  members).
* `Input.restrict?`, `Input.embed`, `Output.embed`: translation of inputs and outputs.
* `Protocol.embed A e`: `A` run by the members only.
* `Run.restrict e ρ`: the run of `A` performed by the members in a run `ρ` of `A.embed e`.

## Main statements

* `Run.state_restrict`, `Run.output_restrict`, `Run.trace_restrict`: the states, outputs and
  traces of the members are those of the restricted run; `Run.output_eq_nil_of_inv_eq_none`:
  non-members produce no outputs. In membership form: `Run.mem_input_restrict`,
  `Run.mem_output_restrict`.
* `Run.Valid.restrict`, `Run.Valid.satisfies_restrict`: the restriction of a valid run is valid
  for every bound on the number of faulty members, so the specifications satisfied by `A` hold for
  it.
* `Run.bitsSent_restrict`, `Run.bitsSent_eq_zero_of_inv_eq_none`, `Run.bitsSent_embed_le`: the
  bits sent by the members are those of the restricted run; non-members send nothing.
* `Protocol.requestQuiet_embed`, `Protocol.SendsWhileActive.embed`: request-quietness and
  activity windows are preserved by embedding.
-/

@[expose] public section

namespace Cslib.Distributed

/-! ### Sub-process types -/

/-- An embedding of the processes `Q` into the processes `P` together with its partial inverse:
`Q` is a copy of a set of processes inside `P` (the *members*). Typically `Q` is the subtype `↥X`
of a committee `X : Finset P` (`SubProcesses.ofFinset`). The partial inverse lets an embedded
protocol identify the senders of its messages (`Input.restrict?`). -/
structure SubProcesses (Q P : Type*) where
  /-- The process of `P` corresponding to a process of `Q`. -/
  emb : Q → P
  /-- The process of `Q` corresponding to a process of `P`, if it is a member. -/
  inv : P → Option Q
  /-- `inv` is a left inverse of `emb`. -/
  inv_emb (q : Q) : inv (emb q) = some q
  /-- `inv` maps only the members to processes of `Q`. -/
  emb_of_inv {p : P} {q : Q} : inv p = some q → emb q = p

namespace SubProcesses

variable {R Q P : Type*} (e : SubProcesses Q P)

attribute [simp] inv_emb

theorem emb_injective : Function.Injective e.emb := fun a b h =>
  Option.some_injective _ <| by rw [← e.inv_emb a, ← e.inv_emb b, h]

@[simp]
theorem emb_inj {a b : Q} : e.emb a = e.emb b ↔ a = b :=
  e.emb_injective.eq_iff

theorem inv_eq_some_iff {p : P} {q : Q} : e.inv p = some q ↔ e.emb q = p :=
  ⟨e.emb_of_inv, fun h => h ▸ e.inv_emb q⟩

theorem inv_eq_none_iff {p : P} : e.inv p = none ↔ ∀ q, e.emb q ≠ p := by
  rw [Option.eq_none_iff_forall_ne_some]
  exact forall_congr' fun q => not_congr e.inv_eq_some_iff

/-- A sub-process type is determined by its embedding. -/
@[ext]
theorem ext {e₁ e₂ : SubProcesses Q P} (h : ∀ q, e₁.emb q = e₂.emb q) : e₁ = e₂ := by
  obtain ⟨emb₁, inv₁, inv_emb₁, emb_of_inv₁⟩ := e₁
  obtain ⟨emb₂, inv₂, inv_emb₂, emb_of_inv₂⟩ := e₂
  obtain rfl : emb₁ = emb₂ := funext h
  obtain rfl : inv₁ = inv₂ := funext fun p => Option.ext fun q => by
    exact ⟨fun h => emb_of_inv₁ h ▸ inv_emb₂ q, fun h => emb_of_inv₂ h ▸ inv_emb₁ q⟩
  rfl

/-- The embedding of `Q` into `P`. -/
def toEmbedding : Q ↪ P := ⟨e.emb, e.emb_injective⟩

@[simp]
theorem toEmbedding_apply (q : Q) : e.toEmbedding q = e.emb q := rfl

/-- Composition of sub-process types: `R` inside `Q` inside `P`. -/
@[simps emb]
def trans (e₁ : SubProcesses R Q) (e₂ : SubProcesses Q P) : SubProcesses R P where
  emb r := e₂.emb (e₁.emb r)
  inv p := (e₂.inv p).bind e₁.inv
  inv_emb r := by simp
  emb_of_inv h := by
    obtain ⟨q, hq, hr⟩ := Option.bind_eq_some_iff.1 h
    rw [e₁.emb_of_inv hr, e₂.emb_of_inv hq]

/-! #### Members -/

section Members

variable [Fintype Q]

/-- The members: the processes of `P` that are processes of `Q`. -/
def members : Finset P := Finset.univ.map e.toEmbedding

variable {e}

theorem mem_members {p : P} : p ∈ e.members ↔ ∃ q, e.emb q = p := by
  simp [members]

@[simp]
theorem emb_mem_members (q : Q) : e.emb q ∈ e.members :=
  mem_members.2 ⟨q, rfl⟩

theorem mem_members_iff_isSome {p : P} : p ∈ e.members ↔ (e.inv p).isSome := by
  rw [mem_members, Option.isSome_iff_exists]
  exact exists_congr fun q => e.inv_eq_some_iff.symm

theorem card_members : e.members.card = Fintype.card Q := by
  simp [members]

end Members

/-! #### Members of a set of processes -/

/-- The members of a set of processes `F`, as processes of `Q` (e.g. the faulty members). -/
def preimage (F : Finset P) : Finset Q :=
  F.filterMap e.inv fun _ _ _ h₁ h₂ => (e.emb_of_inv h₁).symm.trans (e.emb_of_inv h₂)

variable {e} {F : Finset P}

@[simp]
theorem mem_preimage {q : Q} : q ∈ e.preimage F ↔ e.emb q ∈ F := by
  simp only [preimage, Finset.mem_filterMap, inv_eq_some_iff]
  exact ⟨fun ⟨p, hp, h⟩ => h ▸ hp, fun h => ⟨_, h, rfl⟩⟩

/-- The members of `F`, embedded back into `P`, are the elements of `F` that are members. -/
theorem map_preimage : (e.preimage F).map e.toEmbedding = F.filter fun p => (e.inv p).isSome := by
  ext p
  simp only [Finset.mem_map, mem_preimage, toEmbedding_apply, Finset.mem_filter,
    Option.isSome_iff_exists, inv_eq_some_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq, q, rfl⟩
  · rintro ⟨hp, q, rfl⟩
    exact ⟨q, hp, rfl⟩

/-- The number of members of `F`. -/
theorem card_preimage : (e.preimage F).card = (F.filter fun p => (e.inv p).isSome).card := by
  rw [← map_preimage, Finset.card_map]

theorem card_preimage_le : (e.preimage F).card ≤ F.card :=
  card_preimage.trans_le (Finset.card_filter_le _ _)

theorem preimage_trans {e₁ : SubProcesses R Q} {e₂ : SubProcesses Q P} :
    (e₁.trans e₂).preimage F = e₁.preimage (e₂.preimage F) := by
  ext r
  simp

/-! #### Committees -/

section Finset

variable [DecidableEq P]

/-- A committee `X : Finset P`, as the sub-process type `↥X` of `P`. -/
@[simps emb]
def ofFinset (X : Finset P) : SubProcesses X P where
  emb := Subtype.val
  inv p := if h : p ∈ X then some ⟨p, h⟩ else none
  inv_emb q := by simp
  emb_of_inv {p q} h := by
    split_ifs at h with hp
    · cases h
      rfl

/-- A committee `X` inside a committee `C ⊇ X`, as the sub-process type `↥X` of `↥C`. -/
@[simps emb]
def ofSubset {X C : Finset P} (h : X ⊆ C) : SubProcesses X C where
  emb q := ⟨q.1, h q.2⟩
  inv p := if hp : p.1 ∈ X then some ⟨p.1, hp⟩ else none
  inv_emb q := by simp
  emb_of_inv {p q} h := by
    split_ifs at h with hp
    · cases h
      rfl

@[simp]
theorem ofFinset_inv_eq_none {X : Finset P} {p : P} : (ofFinset X).inv p = none ↔ p ∉ X := by
  simp [ofFinset]

@[simp]
theorem ofSubset_inv_eq_none {X C : Finset P} (h : X ⊆ C) {p : C} :
    (ofSubset h).inv p = none ↔ p.1 ∉ X := by
  simp [ofSubset]

/-- The members of a committee `X` inside a committee `C ⊇ X` are the elements of `X`. -/
theorem mem_members_ofSubset {X C : Finset P} (h : X ⊆ C) {p : C} :
    p ∈ (ofSubset h).members ↔ p.1 ∈ X := by
  rw [mem_members]
  exact ⟨fun ⟨q, hq⟩ => hq ▸ q.2, fun hp => ⟨⟨p.1, hp⟩, rfl⟩⟩

/-- The number of members of `X` in `F`. -/
theorem card_preimage_ofFinset (X F : Finset P) :
    ((ofFinset X).preimage F).card = (F ∩ X).card := by
  rw [card_preimage, ← Finset.filter_mem_eq_inter]
  congr 1
  ext p
  simp [ofFinset, apply_dite]

theorem ofSubset_trans_ofFinset {X C : Finset P} (h : X ⊆ C) :
    (ofSubset h).trans (ofFinset C) = ofFinset X := by
  ext
  rfl

theorem ofSubset_trans_ofSubset {X Y C : Finset P} (h₁ : X ⊆ Y) (h₂ : Y ⊆ C) :
    (ofSubset h₁).trans (ofSubset h₂) = ofSubset (h₁.trans h₂) := by
  ext
  rfl

/-- The number of members of a subcommittee `Y ⊆ C` in a set `F` of processes of `C`: the number
of processes of `F`, as processes of `P`, in `Y`. -/
theorem card_preimage_ofSubset {Y C : Finset P} (h : Y ⊆ C) (F : Finset C) :
    ((ofSubset h).preimage F).card = (F.map (Function.Embedding.subtype (· ∈ C)) ∩ Y).card := by
  have hF : (ofFinset C).preimage (F.map (Function.Embedding.subtype (· ∈ C))) = F := by
    ext q
    simp
  rw [← card_preimage_ofFinset, ← ofSubset_trans_ofFinset h, preimage_trans, hF]

end Finset

end SubProcesses

/-! ### Inputs and outputs of members -/

section InputOutput

variable {Q P Msg Timer Req Ind : Type*} (e : SubProcesses Q P)

/-- The input of a member corresponding to an input of `Q`: the sender of a message is
embedded. -/
def Input.embed : Input Q Msg Timer Req → Input P Msg Timer Req
  | .req r => .req r
  | .recv q m => .recv (e.emb q) m
  | .timeout k => .timeout k

/-- The input of `Q` corresponding to an input of a member, if any: messages from non-members are
dropped. -/
def Input.restrict? : Input P Msg Timer Req → Option (Input Q Msg Timer Req)
  | .req r => some (.req r)
  | .recv p m => (e.inv p).map fun q => .recv q m
  | .timeout k => some (.timeout k)

/-- The output of a member corresponding to an output of `Q`: the recipient of a message is
embedded. -/
def Output.embed : Output Q Msg Timer Ind → Output P Msg Timer Ind
  | .send q m => .send (e.emb q) m
  | .ind i => .ind i
  | .setTimer k T => .setTimer k T

variable {e}

@[simp] theorem Input.embed_req (r : Req) :
    (Input.req r : Input Q Msg Timer Req).embed e = .req r := rfl
@[simp] theorem Input.embed_recv (q : Q) (m : Msg) :
    (Input.recv q m : Input Q Msg Timer Req).embed e = .recv (e.emb q) m := rfl
@[simp] theorem Input.embed_timeout (k : Timer) :
    (Input.timeout k : Input Q Msg Timer Req).embed e = .timeout k := rfl

@[simp] theorem Output.embed_send (q : Q) (m : Msg) :
    (Output.send q m : Output Q Msg Timer Ind).embed e = .send (e.emb q) m := rfl
@[simp] theorem Output.embed_ind (i : Ind) :
    (Output.ind i : Output Q Msg Timer Ind).embed e = .ind i := rfl
@[simp] theorem Output.embed_setTimer (k : Timer) (T : ℕ) :
    (Output.setTimer k T : Output Q Msg Timer Ind).embed e = .setTimer k T := rfl

/-- An input of a member is kept as `y` iff it is the embedding of `y`. -/
@[simp]
theorem Input.restrict?_eq_some_iff {x : Input P Msg Timer Req} {y : Input Q Msg Timer Req} :
    x.restrict? e = some y ↔ y.embed e = x := by
  rcases x with r | ⟨p, m⟩ | k <;> rcases y with r' | ⟨q, m'⟩ | k' <;>
    simp [Input.restrict?, Input.embed, SubProcesses.inv_eq_some_iff] <;> grind

@[simp]
theorem Input.restrict?_embed (y : Input Q Msg Timer Req) : (y.embed e).restrict? e = some y :=
  Input.restrict?_eq_some_iff.2 rfl

@[simp]
theorem Input.req?_embed (y : Input Q Msg Timer Req) : (y.embed e).req? = y.req? := by
  cases y <;> rfl

theorem Output.embed_injective :
    Function.Injective (Output.embed e : Output Q Msg Timer Ind → Output P Msg Timer Ind) := by
  intro o₁ o₂ h
  rcases o₁ with ⟨q₁, m₁⟩ | i₁ | ⟨k₁, T₁⟩ <;> rcases o₂ with ⟨q₂, m₂⟩ | i₂ | ⟨k₂, T₂⟩ <;>
    simp_all [Output.embed]

@[simp]
theorem Output.embed_inj {o₁ o₂ : Output Q Msg Timer Ind} : o₁.embed e = o₂.embed e ↔ o₁ = o₂ :=
  Output.embed_injective.eq_iff

@[simp]
theorem Output.ind?_embed (o : Output Q Msg Timer Ind) : (o.embed e).ind? = o.ind? := by
  cases o <;> rfl

@[simp]
theorem Output.bits_embed (size : Msg → ℕ) (o : Output Q Msg Timer Ind) :
    (o.embed e).bits size = o.bits size := by
  cases o <;> rfl

end InputOutput

/-! ### Embedded protocols -/

namespace Embed

variable {Q P : Type*} {I : Interface} (A : Protocol Q I) (e : SubProcesses Q P)

/-- The step of process `p` in `A.embed e`: a member with a state handles the inputs that are
kept by `Input.restrict?` as `A` does; everything else changes nothing and produces no
outputs. -/
def step (p : P) (now : ℕ) (x : Input P A.Msg A.Timer I.Req) (s : Option A.State) :
    Option A.State × List (Output P A.Msg A.Timer I.Ind) :=
  match e.inv p, x.restrict? e, s with
  | some q, some y, some s =>
    (some (A.step q now y s).1, (A.step q now y s).2.map (Output.embed e))
  | _, _, s => (s, [])

end Embed

variable {Q P : Type*} {I : Interface}

/-- The protocol `A` for the processes `Q`, run by the members `e.emb q` of `P`: a member `e.emb q`
behaves as `q` in `A` (with state `some s`), messages from non-members are dropped, and
non-members are inert (state `none`, no outputs). Messages and timers are those of `A`.

The definition is reducible so that the message and timer types unfold to those of `A`. -/
abbrev Protocol.embed (A : Protocol Q I) (e : SubProcesses Q P) : Protocol P I where
  Msg := A.Msg
  Timer := A.Timer
  State := Option A.State
  init p := (e.inv p).map A.init
  step := Embed.step A e

namespace Embed

variable {A : Protocol Q I} {e : SubProcesses Q P}

theorem step_of_restrict?_eq_some {q : Q} {now : ℕ} {x : (A.embed e).In} {y : A.In}
    (h : x.restrict? e = some y) (s : A.State) :
    step A e (e.emb q) now x (some s) =
      (some (A.step q now y s).1, (A.step q now y s).2.map (Output.embed e)) := by
  simp only [step, SubProcesses.inv_emb, h]

theorem step_of_restrict?_eq_none {p : P} {now : ℕ} {x : (A.embed e).In}
    (h : x.restrict? e = none) (s : (A.embed e).State) : step A e p now x s = (s, []) := by
  simp only [step, h]
  split <;> simp_all

theorem step_of_inv_eq_none {p : P} (h : e.inv p = none) (now : ℕ) (x : (A.embed e).In)
    (s : (A.embed e).State) : step A e p now x s = (s, []) := by
  simp only [step, h]

end Embed

namespace Protocol

variable {A : Protocol Q I} {e : SubProcesses Q P}

/-- A member that handles a batch of inputs handles the inputs kept by `Input.restrict?` as `A`
does: the states correspond, and the steps produce the same lists (via `G` and `G'`) provided
dropped inputs produce nothing via `G` and kept inputs produce the same via `G` and `G'`. -/
theorem batch_embed {γ : Type*} {G : (A.embed e).In × List (A.embed e).Out → List γ}
    {G' : A.In × List A.Out → List γ} (hdrop : ∀ x, x.restrict? e = none → G (x, []) = [])
    (hkeep : ∀ x y os, x.restrict? e = some y → G (x, os.map (Output.embed e)) = G' (y, os))
    (q : Q) (now : ℕ) (xs : List (A.embed e).In) (s : A.State) :
    ((A.embed e).batch (e.emb q) now xs (some s)).1 =
        some (A.batch q now (xs.filterMap (Input.restrict? e)) s).1 ∧
      ((A.embed e).batch (e.emb q) now xs (some s)).2.flatMap G =
        (A.batch q now (xs.filterMap (Input.restrict? e)) s).2.flatMap G' := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    rcases hx : x.restrict? e with _ | y
    · simp only [batch_cons, Embed.step_of_restrict?_eq_none hx, List.filterMap_cons, hx,
        List.flatMap_cons, hdrop x hx, List.nil_append]
      exact ih s
    · simp only [batch_cons, Embed.step_of_restrict?_eq_some hx, List.filterMap_cons, hx,
        List.flatMap_cons, hkeep x y _ hx]
      exact ⟨(ih _).1, congrArg _ (ih _).2⟩

/-- Embedding preserves request-quietness. -/
theorem requestQuiet_embed (hA : A.RequestQuiet) : (A.embed e).RequestQuiet := by
  intro p now r s i hi
  rcases hp : e.inv p with _ | q
  · simp [Embed.step_of_inv_eq_none hp] at hi
  · obtain rfl := e.emb_of_inv hp
    rcases s with _ | s
    · simp [Embed.step] at hi
    · rw [show (A.embed e).step (e.emb q) now (.req r) (some s) = _ from
        Embed.step_of_restrict?_eq_some (x := .req r) (y := .req r) rfl s] at hi
      obtain ⟨o, ho, h⟩ := List.mem_map.1 hi
      cases o <;> cases h
      exact hA q now r s i ho

end Protocol

/-! ### Restriction of runs to the members -/

namespace Run

variable {A : Protocol Q I} (e : SubProcesses Q P)

/-- The run of `A` performed by the members in a run of `A.embed e`: the faulty members, the same
GST, and the clocks and inputs of the members, without the messages from non-members. -/
@[simps faulty gst clock]
def restrict (ρ : Run (A.embed e)) : Run A where
  faulty := e.preimage ρ.faulty
  gst := ρ.gst
  clock q := ρ.clock (e.emb q)
  input q τ := (ρ.input (e.emb q) τ).filterMap (Input.restrict? e)

variable {e} {ρ : Run (A.embed e)}

theorem mem_restrict_faulty {q : Q} : q ∈ (ρ.restrict e).faulty ↔ e.emb q ∈ ρ.faulty := by
  simp

/-- The state of a member is the state of the restricted run. -/
theorem state_restrict (q : Q) (τ : ℕ) : ρ.state (e.emb q) τ = some ((ρ.restrict e).state q τ) := by
  induction τ with
  | zero => simp
  | succ τ ih =>
    rw [state_succ, state_succ, ih]
    exact (Protocol.batch_embed (G := fun _ => ([] : List Unit)) (G' := fun _ => [])
      (fun _ _ => rfl) (fun _ _ _ _ => rfl) q _ _ _).1

private theorem flatMap_steps_restrict {γ : Type*}
    {G : (A.embed e).In × List (A.embed e).Out → List γ} {G' : A.In × List A.Out → List γ}
    (hdrop : ∀ x, x.restrict? e = none → G (x, []) = [])
    (hkeep : ∀ x y os, x.restrict? e = some y → G (x, os.map (Output.embed e)) = G' (y, os))
    (q : Q) (τ : ℕ) : (ρ.steps (e.emb q) τ).flatMap G = ((ρ.restrict e).steps q τ).flatMap G' := by
  rw [steps, steps, state_restrict]
  exact (Protocol.batch_embed hdrop hkeep q _ _ _).2

/-- The outputs of a member are the outputs of the restricted run, embedded. -/
theorem output_restrict (q : Q) (τ : ℕ) :
    ρ.output (e.emb q) τ = ((ρ.restrict e).output q τ).map (Output.embed e) := by
  rw [output, output, List.map_flatMap]
  exact flatMap_steps_restrict (fun _ _ => rfl) (fun _ _ _ _ => rfl) q τ

/-- The trace of a member is the trace of the restricted run. -/
theorem trace_restrict (q : Q) (τ : ℕ) : (ρ.restrict e).trace q τ = ρ.trace (e.emb q) τ := by
  refine (flatMap_steps_restrict (fun x hx => ?_) (fun x y os hx => ?_) q τ).symm
  · cases x with
    | req r => simp [Input.restrict?] at hx
    | recv p m => rfl
    | timeout k => simp [Input.restrict?] at hx
  · obtain rfl := Input.restrict?_eq_some_iff.1 hx
    simp [stepEvents, List.filterMap_map]

/-- Non-members produce no outputs. -/
theorem output_eq_nil_of_inv_eq_none {p : P} (h : e.inv p = none) (τ : ℕ) : ρ.output p τ = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro o ho
  obtain ⟨_, x, _, -, ho⟩ := mem_output_iff.1 ho
  simp [Embed.step_of_inv_eq_none h] at ho

/-- The inputs of the restricted run are the inputs of the member that are kept. -/
@[simp]
theorem mem_input_restrict {q : Q} {τ : ℕ} {y : A.In} :
    y ∈ (ρ.restrict e).input q τ ↔ y.embed e ∈ ρ.input (e.emb q) τ := by
  simp [restrict, List.mem_filterMap]

/-- The outputs of the restricted run are the outputs of the member. -/
@[simp]
theorem mem_output_restrict {q : Q} {τ : ℕ} {o : A.Out} :
    o ∈ (ρ.restrict e).output q τ ↔ o.embed e ∈ ρ.output (e.emb q) τ := by
  simp [output_restrict]

/-! #### Validity -/

variable {t δ t' : ℕ}

/-- The restriction of a valid run is valid, for every bound `t'` on the number of faulty
members. -/
theorem Valid.restrict (hρ : ρ.Valid t δ) (ht : (e.preimage ρ.faulty).card ≤ t') :
    (ρ.restrict e).Valid t' δ where
  card_faulty_le := ht
  clock_mono q := hρ.clock_mono (e.emb q)
  clock_succ := hρ.clock_succ
  authentic hp hq h := by
    rw [mem_restrict_faulty] at hp hq
    obtain ⟨τ', hτ', h', hd⟩ := hρ.authentic hp hq (mem_input_restrict.1 h)
    exact ⟨τ', hτ', mem_output_restrict.2 h', hd⟩
  reliable hp hq h := by
    rw [mem_restrict_faulty] at hp hq
    obtain ⟨τ', h₁, h₂, h'⟩ := hρ.reliable hp hq (mem_output_restrict.1 h)
    exact ⟨τ', h₁, h₂, mem_input_restrict.2 h'⟩
  timer hp := by
    rw [mem_restrict_faulty] at hp
    rw [mem_input_restrict, Input.embed_timeout, hρ.timer hp]
    simp only [mem_output_restrict, Output.embed_setTimer]
    rfl

/-- Specifications satisfied by `A` hold for the restriction of a valid run of `A.embed e`, if
at most `t'` members are faulty. -/
theorem Valid.satisfies_restrict (hρ : ρ.Valid t δ) {S : Spec Q I} (hA : A.Satisfies t' δ S)
    (ht : (e.preimage ρ.faulty).card ≤ t') : S (ρ.restrict e).history :=
  hA _ (hρ.restrict ht)

/-! #### Bits -/

/-- A member sends the bits of the restricted run. -/
theorem bitsSent_restrict (size : A.Msg → ℕ) (q : Q) (a b : ℕ) :
    ρ.bitsSent size (e.emb q) a b = (ρ.restrict e).bitsSent size q a b := by
  simp only [bitsSent_eq_sum_Ico, output_restrict, List.map_map, Function.comp_def,
    Output.bits_embed]

/-- Non-members send no bits. -/
theorem bitsSent_eq_zero_of_inv_eq_none (size : A.Msg → ℕ) {p : P} (h : e.inv p = none)
    (a b : ℕ) : ρ.bitsSent size p a b = 0 :=
  bitsSent_eq_zero fun τ _ _ q m => by simp [output_eq_nil_of_inv_eq_none h]

variable (ρ) in
/-- **Bits of an embedded protocol**: a bound `M q` on the bits sent by `q` in the restricted run
bounds the bits sent by the member `e.emb q`, and a non-member sends nothing. -/
theorem bitsSent_embed_le (size : A.Msg → ℕ) {a b : ℕ} {M : Q → ℕ}
    (hM : ∀ q, (ρ.restrict e).bitsSent size q a b ≤ M q) (p : P) :
    ρ.bitsSent size p a b ≤ (e.inv p).elim 0 M := by
  cases h : e.inv p with
  | none => rw [bitsSent_eq_zero_of_inv_eq_none size h]; exact Nat.zero_le _
  | some q =>
    rw [← e.emb_of_inv h, bitsSent_restrict]
    exact hM q

end Run

/-- Embedding preserves activity windows. -/
theorem Protocol.SendsWhileActive.embed {A : Protocol Q I} {start stop : I.Req → Prop}
    (h : A.SendsWhileActive start stop) (e : SubProcesses Q P) :
    (A.embed e).SendsWhileActive start stop := by
  intro ρ p τ p' m hm
  rcases hp : e.inv p with _ | q
  · simp [Run.output_eq_nil_of_inv_eq_none hp] at hm
  · obtain rfl := e.emb_of_inv hp
    rw [Run.output_restrict] at hm
    obtain ⟨o, ho, ho'⟩ := List.mem_map.1 hm
    rcases o with ⟨q', m'⟩ | i | ⟨k, T⟩ <;> cases ho'
    obtain ⟨⟨τ', hτ', r, hr, hin⟩, hstop⟩ := h _ q τ q' m ho
    refine ⟨⟨τ', hτ', r, hr, by simpa using hin⟩, fun τ'' hτ'' r hr hin => ?_⟩
    exact hstop τ'' hτ'' r hr (Run.mem_input_restrict.2 hin)

end Cslib.Distributed
