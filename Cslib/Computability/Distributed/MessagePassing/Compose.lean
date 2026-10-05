/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.MessagePassing.Spec

/-! # Composition of message-passing protocols

Protocols are commonly built from sub-protocols ("Uses: … instances …" in module-style
pseudocode). We model this as follows. A parent *logic* is a protocol over the extended
interface `I.uses J`: besides the requests of `I` it handles the indications of children with
interfaces `J i`, and besides the indications of `I` it emits requests to the children. Given
children `C i : Protocol P (J i)`, the composite `L.compose C : Protocol P I` runs the logic and
all children side by side at every process. When the composite handles an input, the input is
dispatched to the logic or to a child; indications of a child are fed to the logic as requests
and requests of the logic are fed to the children, all within the same zero-time step.

To keep the composite step a total, non-recursive function, indications that a child emits
while handling a *request* are not routed (they are dropped). The children of interest are
*request-quiet* (`Protocol.RequestQuiet`), so nothing is lost.

## Main definitions

* `Interface.uses I J`: the interface of a logic using children with interfaces `J i`.
* `Protocol.compose L C`: the composite protocol.
* `Run.logic`, `Run.child`: the projections of a run of the composite onto the logic and onto
  each child.

## Main statements

The projection theorem: for a valid run `ρ` of the composite,
* `Run.Valid.child`, `Run.Valid.logic`: the projections are valid runs (same faulty processes,
  GST and clocks), and `Run.state_compose`: the composite state is assembled from their states;
* `Run.child_reqs`, `Run.child_inds`: the requests handled by child `i` are the requests to `i`
  emitted by the logic, and (if `C i` is request-quiet) the indications of child `i` are the
  indications of `i` handled by the logic, in order;
* `Run.trace_compose`: the trace of the composite is the trace of the logic restricted to `I`.

In the form used for specifications (`Run.history_reqAt_compose`, `Run.history_indAt_compose`,
`Run.history_reqAt_child`, `Run.history_indAt_child`): the requests and indications in the
histories of the composite and of the children are the corresponding inputs and outputs of the
logic.

Consequently (`Run.Valid.satisfies_child`) specifications satisfied by the children hold for
the child projections of every valid run of the composite. Their environment assumptions of
the form "at most one request of a kind" follow from the logic (`Run.atMostOnce_child_of_logic`).
-/

@[expose] public section

namespace Cslib.Distributed

/-! ### Fibres of sigma types -/

section sigmaGet

variable {α ι : Type*} [DecidableEq ι] {X : ι → Type*}

/-- The value of `e : Σ j, X j` if `e` lies over `i`. -/
def sigmaGet? (i : ι) (e : Σ j, X j) : Option (X i) :=
  if h : e.1 = i then some (h ▸ e.2) else none

@[simp]
theorem sigmaGet?_mk (i : ι) (x : X i) : sigmaGet? i ⟨i, x⟩ = some x := by
  simp [sigmaGet?]

@[simp]
theorem sigmaGet?_eq_some_iff {i : ι} {e : Σ j, X j} {x : X i} :
    sigmaGet? i e = some x ↔ e = ⟨i, x⟩ := by
  obtain ⟨j, y⟩ := e
  unfold sigmaGet?
  split_ifs with h
  · subst h
    simp
  · simp only [false_iff]
    rintro ⟨⟩
    exact h rfl

theorem sigmaGet?_mk_of_ne {i j : ι} (h : j ≠ i) (x : X j) : sigmaGet? i ⟨j, x⟩ = none := by
  simp [sigmaGet?, h]

/-- The value of `e : α ⊕ Σ j, X j` if `e` is a right summand lying over `i`. -/
def rightGet? (i : ι) (e : α ⊕ Σ j, X j) : Option (X i) :=
  e.getRight?.bind (sigmaGet? i)

@[simp]
theorem rightGet?_inl (i : ι) (a : α) : rightGet? (X := X) i (.inl a) = none := rfl

@[simp]
theorem rightGet?_inr (i : ι) (e : Σ j, X j) : rightGet? (α := α) i (.inr e) = sigmaGet? i e :=
  rfl

@[simp]
theorem rightGet?_eq_some_iff {i : ι} {e : α ⊕ Σ j, X j} {x : X i} :
    rightGet? i e = some x ↔ e = .inr ⟨i, x⟩ := by
  cases e <;> simp

end sigmaGet

/-! ### Interfaces of logics -/

section Interface

variable {ι : Type}

/-- The interface of a parent protocol (a *logic*) for interface `I` that uses children with
interfaces `J i`: it handles the requests of `I` and the indications of the children, and emits
the indications of `I` and requests to the children.

`simp` lemmas about the requests or indications of a concrete logic should be stated over
unfolded aliases of `I.Req ⊕ Σ i, (J i).Ind` and `I.Ind ⊕ Σ i, (J i).Req`, not over
`(I.uses J).Req` or `(I.uses J).Ind`: the `dsimp` pass of `simp` reduces the projection of this
structure literal in the goal, so a lemma whose keys mention `(I.uses J).Req` never matches. -/
abbrev Interface.uses (I : Interface) (J : ι → Interface) : Interface where
  Req := I.Req ⊕ Σ i, (J i).Ind
  Ind := I.Ind ⊕ Σ i, (J i).Req

variable {I : Interface} {J : ι → Interface}

/-- The event of the parent interface `I` corresponding to an event of the extended interface
`I.uses J`, if any. -/
def Event.parent? : Event (I.uses J) → Option (Event I)
  | .req (.inl r) => some (.req r)
  | .ind (.inl i) => some (.ind i)
  | _ => none

/-- A logic is *parent-request-quiet* if handling a request of the parent interface never emits
an indication of the parent interface (requests to children are allowed). -/
def Protocol.ParentRequestQuiet {P : Type*} (L : Protocol P (I.uses J)) : Prop :=
  ∀ (p : P) (now : ℕ) (r : I.Req) (s : L.State) (i : I.Ind),
    .ind (.inl i) ∉ (L.step p now (.req (.inl r)) s).2

end Interface

/-! ### The composite protocol -/

namespace Compose

variable {P : Type*} {I : Interface} {ι : Type} {J : ι → Interface}
  (L : Protocol P (I.uses J)) (C : (i : ι) → Protocol P (J i))

/-- Messages of the composite: messages of the logic or of some child. -/
abbrev Msg := L.Msg ⊕ Σ i, (C i).Msg

/-- Timer tags of the composite: timer tags of the logic or of some child. -/
abbrev Timer := L.Timer ⊕ Σ i, (C i).Timer

/-- States of the composite: a state of the logic and a state of every child. -/
abbrev State := L.State × ((i : ι) → (C i).State)

/-- A step taken by a component while the composite handles an input: a step of the logic or a
step of some child, each recorded with its input and outputs. -/
abbrev Entry := (L.In × List L.Out) ⊕ Σ i, (C i).In × List (C i).Out

/-- The component that handles an input of the composite first, with the corresponding input. -/
def dispatch : Input P (Msg L C) (Timer L C) I.Req → L.In ⊕ Σ j, (C j).In
  | .req r => .inl (.req (.inl r))
  | .recv q (.inl m) => .inl (.recv q m)
  | .recv q (.inr ⟨j, m⟩) => .inr ⟨j, .recv q m⟩
  | .timeout (.inl k) => .inl (.timeout k)
  | .timeout (.inr ⟨j, k⟩) => .inr ⟨j, .timeout k⟩

/-- The external output corresponding to an output of the logic, if any. -/
def liftLogic : L.Out → Option (Output P (Msg L C) (Timer L C) I.Ind)
  | .send q m => some (.send q (.inl m))
  | .ind (.inl i) => some (.ind i)
  | .ind (.inr _) => none
  | .setTimer k T => some (.setTimer (.inl k) T)

/-- The external output corresponding to an output of child `j`, if any. -/
def liftChild (j : ι) : (C j).Out → Option (Output P (Msg L C) (Timer L C) I.Ind)
  | .send q m => some (.send q (.inr ⟨j, m⟩))
  | .ind _ => none
  | .setTimer k T => some (.setTimer (.inr ⟨j, k⟩) T)

/-- The external outputs of a component step. -/
def externalOutputs : Entry L C → List (Output P (Msg L C) (Timer L C) I.Ind)
  | .inl e => e.2.filterMap (liftLogic L C)
  | .inr ⟨j, e⟩ => e.2.filterMap (liftChild L C j)

variable [DecidableEq ι] (p : P) (now : ℕ)

/-- Child `j` handles input `y`; its outputs are recorded but not routed. -/
def childStep (j : ι) (y : (C j).In) (s : State L C) : State L C × List (Entry L C) :=
  let o := (C j).step p now y (s.2 j)
  ((s.1, Function.update s.2 j o.1), [.inr ⟨j, (y, o.2)⟩])

/-- Routing of a logic output: a request to child `j` is handled by child `j` (indications it
emits in response are not routed); other outputs are external and need no routing. -/
def routeLogic : L.Out → State L C → State L C × List (Entry L C)
  | .ind (.inr ⟨j, r⟩), s => childStep L C p now j (.req r) s
  | _, s => (s, [])

/-- The logic handles input `y`, then its requests to the children are routed. -/
def logicIn (y : L.In) (s : State L C) : State L C × List (Entry L C) :=
  let o := L.step p now y s.1
  let r := foldSteps (routeLogic L C p now) o.2 (o.1, s.2)
  (r.1, .inl (y, o.2) :: r.2)

/-- Routing of an output of child `j`: an indication is handled by the logic (with routing of
its requests); other outputs are external and need no routing. -/
def routeChild (j : ι) : (C j).Out → State L C → State L C × List (Entry L C)
  | .ind x, s => logicIn L C p now (.req (.inr ⟨j, x⟩)) s
  | _, s => (s, [])

/-- Child `j` handles input `y`, then its indications are routed to the logic. -/
def childIn (j : ι) (y : (C j).In) (s : State L C) : State L C × List (Entry L C) :=
  let r := childStep L C p now j y s
  let r' := foldSteps (routeChild L C p now j) ((C j).step p now y (s.2 j)).2 r.1
  (r'.1, r.2 ++ r'.2)

/-- The composite handles one input: the new state and the component steps taken, in order. -/
def handle (x : Input P (Msg L C) (Timer L C) I.Req) (s : State L C) :
    State L C × List (Entry L C) :=
  match dispatch L C x with
  | .inl y => logicIn L C p now y s
  | .inr ⟨j, y⟩ => childIn L C p now j y s

end Compose

variable {P : Type*} {I : Interface} {ι : Type} {J : ι → Interface} [DecidableEq ι]

/-- The composition of a logic `L` with children `C i`: every process runs the logic and all the
children; inputs are dispatched to the component they belong to, indications of the children
are handled by the logic and requests of the logic by the children, in the same zero-time step.

The definition is reducible so that the message and timer types of the composite unfold to sums.
-/
abbrev Protocol.compose (L : Protocol P (I.uses J)) (C : (i : ι) → Protocol P (J i)) :
    Protocol P I where
  Msg := Compose.Msg L C
  Timer := Compose.Timer L C
  State := Compose.State L C
  init p := (L.init p, fun i => (C i).init p)
  step p now x s :=
    ((Compose.handle L C p now x s).1,
      (Compose.handle L C p now x s).2.flatMap (Compose.externalOutputs L C))

/-! ### Structure of the composite step -/

namespace Compose

variable {L : Protocol P (I.uses J)} {C : (i : ι) → Protocol P (J i)} {p : P} {now : ℕ}

section rel

variable {R : State L C → List (Entry L C) → State L C → Prop}

private theorem logicIn_rel (nil : ∀ s, R s [] s)
    (append : ∀ {s₁ l₁ s₂ l₂ s₃}, R s₁ l₁ s₂ → R s₂ l₂ s₃ → R s₁ (l₁ ++ l₂) s₃)
    (hlogic : ∀ y s, R s [.inl (y, (L.step p now y s.1).2)] ((L.step p now y s.1).1, s.2))
    (hchild : ∀ j y s, R s (childStep L C p now j y s).2 (childStep L C p now j y s).1)
    (y : L.In) (s : State L C) : R s (logicIn L C p now y s).2 (logicIn L C p now y s).1 :=
  append (hlogic y s) (foldSteps_rel nil append (fun o _ s => by
    rcases o with _ | (_ | ⟨j, r⟩) | _
    exacts [nil s, nil s, hchild j _ s, nil s]) _)

/-- A relation that holds for the empty list, is closed under concatenation, and holds for
single steps of the logic and of the children holds for the steps taken by `handle`. -/
private theorem handle_rel (nil : ∀ s, R s [] s)
    (append : ∀ {s₁ l₁ s₂ l₂ s₃}, R s₁ l₁ s₂ → R s₂ l₂ s₃ → R s₁ (l₁ ++ l₂) s₃)
    (hlogic : ∀ y s, R s [.inl (y, (L.step p now y s.1).2)] ((L.step p now y s.1).1, s.2))
    (hchild : ∀ j y s, R s (childStep L C p now j y s).2 (childStep L C p now j y s).1)
    (x : Input P (Msg L C) (Timer L C) I.Req) (s : State L C) :
    R s (handle L C p now x s).2 (handle L C p now x s).1 := by
  have hl := logicIn_rel nil append hlogic hchild
  rcases h : dispatch L C x with y | ⟨j, y⟩ <;> simp only [handle, h]
  · exact hl y s
  · exact append (hchild j y s) (foldSteps_rel nil append (fun o _ s => by
      rcases o with _ | x | _
      exacts [nil s, hl _ s, nil s]) _)

end rel

/-- Viewed through `v` and `π`, the component steps `l` are a batch of `A` leading from `v s` to
`v s'`. -/
private def Sim {K : Interface} (A : Protocol P K) (p : P) (now : ℕ) (v : State L C → A.State)
    (π : Entry L C → Option (A.In × List A.Out)) (s : State L C) (l : List (Entry L C))
    (s' : State L C) : Prop :=
  A.batch p now ((l.filterMap π).map Prod.fst) (v s) = (v s', l.filterMap π)

private theorem sim_foldSteps_handle {K : Interface} {A : Protocol P K} {v : State L C → A.State}
    {π : Entry L C → Option (A.In × List A.Out)}
    (hlogic : ∀ y s,
      Sim A p now v π s [.inl (y, (L.step p now y s.1).2)] ((L.step p now y s.1).1, s.2))
    (hchild : ∀ j y s,
      Sim A p now v π s (childStep L C p now j y s).2 (childStep L C p now j y s).1)
    (xs : List (Input P (Msg L C) (Timer L C) I.Req)) (s : State L C) :
    Sim A p now v π s (foldSteps (handle L C p now) xs s).2
      (foldSteps (handle L C p now) xs s).1 := by
  have nil : ∀ s, Sim A p now v π s [] s := fun s => by simp [Sim]
  have append : ∀ {s₁ l₁ s₂ l₂ s₃}, Sim A p now v π s₁ l₁ s₂ → Sim A p now v π s₂ l₂ s₃ →
      Sim A p now v π s₁ (l₁ ++ l₂) s₃ := by
    intro s₁ l₁ s₂ l₂ s₃ h₁ h₂
    unfold Sim at *
    rw [List.filterMap_append, List.map_append, Protocol.batch_append, h₁]
    simp [h₂]
  exact foldSteps_rel nil append (fun x _ s => handle_rel nil append hlogic hchild x s) s

private theorem sim_logic (xs : List (Input P (Msg L C) (Timer L C) I.Req)) (s : State L C) :
    Sim L p now Prod.fst Sum.getLeft? s (foldSteps (handle L C p now) xs s).2
      (foldSteps (handle L C p now) xs s).1 :=
  sim_foldSteps_handle (fun y s => by simp [Sim])
    (fun j y s => by simp [Sim, childStep, List.filterMap_cons]) xs s

private theorem sim_child (i : ι) (xs : List (Input P (Msg L C) (Timer L C) I.Req))
    (s : State L C) :
    Sim (C i) p now (fun s => s.2 i) (rightGet? i) s (foldSteps (handle L C p now) xs s).2
      (foldSteps (handle L C p now) xs s).1 :=
  sim_foldSteps_handle (fun y s => by simp [Sim, List.filterMap_cons]) (fun j y s => by
    by_cases h : j = i
    · subst h
      simp [Sim, childStep]
    · simp [Sim, childStep, sigmaGet?_mk_of_ne h, Function.update_of_ne (Ne.symm h)]) xs s

private theorem batch_compose_fst (xs : List (L.compose C).In) (s : State L C) :
    ((L.compose C).batch p now xs s).1 = (foldSteps (handle L C p now) xs s).1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih _

private theorem flatMap_batch_compose {γ : Type*}
    {G : (L.compose C).In × List (L.compose C).Out → List γ} {g : Entry L C → List γ}
    (h : ∀ x s, G (x, (handle L C p now x s).2.flatMap (externalOutputs L C)) =
      (handle L C p now x s).2.flatMap g)
    (xs : List (L.compose C).In) (s : State L C) :
    ((L.compose C).batch p now xs s).2.flatMap G =
      (foldSteps (handle L C p now) xs s).2.flatMap g := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [Protocol.batch_cons, foldSteps_cons, List.flatMap_cons, List.flatMap_append, ih]
    rw [← h x s]

/-! #### Non-request inputs -/

/-- The input, if it is not a request. -/
private def nonReq? {Msg Timer Req : Type*} :
    Input P Msg Timer Req → Option (Input P Msg Timer Req)
  | .req _ => none
  | y => some y

private theorem nonReq?_eq_some_iff {Msg Timer Req : Type*} {y z : Input P Msg Timer Req} :
    nonReq? y = some z ↔ y = z ∧ y.req? = none := by
  cases y <;> simp [nonReq?, Input.req?, eq_comm]

/-- A component input, if it is not a request. -/
private def netIn : L.In ⊕ (Σ j, (C j).In) → Option (L.In ⊕ Σ j, (C j).In)
  | .inl y => (nonReq? y).map .inl
  | .inr ⟨j, y⟩ => (nonReq? y).map fun y => .inr ⟨j, y⟩

/-- The input of a component step. -/
private def entryInput : Entry L C → L.In ⊕ Σ j, (C j).In
  | .inl (y, _) => .inl y
  | .inr ⟨j, (y, _)⟩ => .inr ⟨j, y⟩

private theorem logicIn_netIn (y : L.In) (s : State L C) :
    (logicIn L C p now y s).2.flatMap (fun e => (netIn (entryInput e)).toList) =
      (netIn (.inl y)).toList := by
  simp only [logicIn, List.flatMap_cons]
  rw [flatMap_foldSteps (h := fun _ => []) fun o _ s => by
    rcases o with _ | (_ | ⟨j, r⟩) | _ <;> simp [routeLogic, childStep, entryInput, netIn, nonReq?]]
  simp [entryInput]

/-- The non-request component inputs while handling `x` are those dispatched from `x`. -/
private theorem handle_netIn (x : Input P (Msg L C) (Timer L C) I.Req) (s : State L C) :
    (handle L C p now x s).2.flatMap (fun e => (netIn (entryInput e)).toList) =
      (netIn (dispatch L C x)).toList := by
  rcases h : dispatch L C x with y | ⟨j, y⟩ <;> simp only [handle, h]
  · exact logicIn_netIn y s
  · simp only [childIn, childStep, List.flatMap_append]
    rw [flatMap_foldSteps (h := fun _ => []) fun o _ s => by
      rcases o with _ | x | _
      · rfl
      · simp only [routeChild]
        rw [logicIn_netIn]
        rfl
      · rfl]
    simp [entryInput]

/-! #### Requests to and indications from the children -/

private theorem logicIn_reqs (i : ι) (y : L.In) (s : State L C) :
    (logicIn L C p now y s).2.flatMap (fun e => ((rightGet? i e).bind fun a => a.1.req?).toList) =
      (logicIn L C p now y s).2.flatMap fun e =>
        e.getLeft?.toList.flatMap fun a => a.2.filterMap fun o => o.ind?.bind (rightGet? i) := by
  simp only [logicIn, List.flatMap_cons]
  rw [flatMap_foldSteps (h := fun o => (o.ind?.bind (rightGet? i)).toList) fun o _ s => by
      rcases o with _ | (_ | ⟨j, r⟩) | _ <;> simp [routeLogic, childStep, Output.ind?]
      by_cases h : j = i
      · subst h
        simp [Input.req?]
      · simp [sigmaGet?_mk_of_ne h],
    flatMap_foldSteps (h := fun _ => []) fun o _ s => by
      rcases o with _ | (_ | ⟨j, r⟩) | _ <;> simp [routeLogic, childStep]]
  simp [List.filterMap_eq_flatMap_toList]

/-- The requests handled by child `i` while handling `x` are the requests to `i` emitted by the
logic. -/
private theorem handle_reqs (i : ι) (x : Input P (Msg L C) (Timer L C) I.Req) (s : State L C) :
    (handle L C p now x s).2.flatMap (fun e => ((rightGet? i e).bind fun a => a.1.req?).toList) =
      (handle L C p now x s).2.flatMap fun e =>
        e.getLeft?.toList.flatMap fun a => a.2.filterMap fun o => o.ind?.bind (rightGet? i) := by
  rcases h : dispatch L C x with y | ⟨j, y⟩ <;> simp only [handle, h]
  · exact logicIn_reqs i y s
  · have hy : y.req? = none := by
      rcases x with _ | ⟨_, _ | ⟨_, _⟩⟩ | (_ | ⟨_, _⟩) <;> cases h <;> rfl
    simp only [childIn, childStep, List.flatMap_append]
    congr 1
    · by_cases h : j = i
      · subst h
        simp [hy]
      · simp [sigmaGet?_mk_of_ne h]
    · refine flatMap_foldSteps_eq (fun o _ s => ?_) _
      rcases o with _ | x | _
      · rfl
      · exact logicIn_reqs i _ s
      · rfl

private theorem logicIn_inds (i : ι) (hC : (C i).RequestQuiet) (y : L.In) (s : State L C) :
    (logicIn L C p now y s).2.flatMap
        (fun e => (rightGet? i e).toList.flatMap fun a => a.2.filterMap Output.ind?) = [] ∧
      (logicIn L C p now y s).2.flatMap
        (fun e => (e.getLeft?.bind fun a => a.1.req?.bind (rightGet? i)).toList) =
        (y.req?.bind (rightGet? i)).toList := by
  simp only [logicIn, List.flatMap_cons]
  rw [flatMap_foldSteps (h := fun _ => []) fun o _ s => by
      rcases o with _ | (_ | ⟨j, r⟩) | _
      · rfl
      · rfl
      · by_cases h : j = i
        · subst h
          simp only [routeLogic, childStep, List.flatMap_cons, List.flatMap_nil, List.append_nil,
            rightGet?_inr, sigmaGet?_mk, Option.toList_some, List.filterMap_eq_nil_iff]
          intro o ho
          cases o
          · rfl
          · exact absurd ho (hC p now r _ _)
          · rfl
        · simp [routeLogic, childStep, sigmaGet?_mk_of_ne h]
      · rfl,
    flatMap_foldSteps (h := fun _ => []) fun o _ s => by
      rcases o with _ | (_ | ⟨j, r⟩) | _ <;> simp [routeLogic, childStep]]
  simp

/-- If child `i` is request-quiet, its indications while handling `x` are the indications from
`i` handled by the logic. -/
private theorem handle_inds (i : ι) (hC : (C i).RequestQuiet)
    (x : Input P (Msg L C) (Timer L C) I.Req) (s : State L C) :
    (handle L C p now x s).2.flatMap
        (fun e => (rightGet? i e).toList.flatMap fun a => a.2.filterMap Output.ind?) =
      (handle L C p now x s).2.flatMap
        (fun e => (e.getLeft?.bind fun a => a.1.req?.bind (rightGet? i)).toList) := by
  rcases h : dispatch L C x with y | ⟨j, y⟩ <;> simp only [handle, h]
  · rw [(logicIn_inds i hC y s).1, (logicIn_inds i hC y s).2]
    rcases x with _ | ⟨_, _ | ⟨_, _⟩⟩ | (_ | ⟨_, _⟩) <;> cases h <;> rfl
  · simp only [childIn, childStep, List.flatMap_append]
    rw [flatMap_foldSteps (h := fun _ => []) fun o _ s => by
        rcases o with _ | x | _
        · rfl
        · exact (logicIn_inds i hC _ s).1
        · rfl,
      flatMap_foldSteps
        (h := fun o => (o.ind?.bind fun x => sigmaGet? (X := fun j => (J j).Ind) i ⟨j, x⟩).toList)
        fun o _ s => by
        rcases o with _ | x | _
        · rfl
        · simp only [routeChild]
          rw [(logicIn_inds i hC _ s).2]
          rfl
        · rfl]
    by_cases h : j = i
    · subst h
      simp [List.filterMap_eq_flatMap_toList]
    · simp [sigmaGet?_mk_of_ne h]

/-! #### Indications to the parent -/

omit [DecidableEq ι] in
private theorem filterMap_externalOutputs_inr (e : Σ j, (C j).In × List (C j).Out) :
    (externalOutputs L C (.inr e)).filterMap (fun o => o.ind?.map Event.ind) = [] := by
  obtain ⟨j, y, os⟩ := e
  simp only [externalOutputs, List.filterMap_filterMap, List.filterMap_eq_nil_iff]
  intro o _
  cases o <;> rfl

omit [DecidableEq ι] in
private theorem filterMap_externalOutputs_inl (a : L.In × List L.Out) :
    (externalOutputs L C (.inl a)).filterMap (fun o => o.ind?.map Event.ind) =
      (a.2.filterMap fun o => o.ind?.map Event.ind).filterMap Event.parent? := by
  simp only [externalOutputs, List.filterMap_filterMap]
  congr 1
  funext o
  rcases o with _ | (_ | _) | _ <;> rfl

private theorem logicIn_events (y : L.In) (s : State L C) :
    (logicIn L C p now y s).2.flatMap
        (fun e => (externalOutputs L C e).filterMap fun o => o.ind?.map Event.ind) =
      ((L.step p now y s.1).2.filterMap fun o => o.ind?.map Event.ind).filterMap Event.parent? ∧
      (logicIn L C p now y s).2.flatMap
        (fun e => e.getLeft?.toList.flatMap fun a => (stepEvents a).filterMap Event.parent?) =
      (stepEvents (y, (L.step p now y s.1).2)).filterMap Event.parent? := by
  simp only [logicIn, List.flatMap_cons]
  rw [flatMap_foldSteps (h := fun _ => []) fun o _ s => by
      rcases o with _ | (_ | ⟨j, r⟩) | _ <;>
        simp [routeLogic, childStep, filterMap_externalOutputs_inr],
    flatMap_foldSteps (h := fun _ => []) fun o _ s => by
      rcases o with _ | (_ | ⟨j, r⟩) | _ <;> simp [routeLogic, childStep]]
  simp [filterMap_externalOutputs_inl]

/-- The indications to the parent emitted while handling `x`, preceded by `x` if it is a request,
are the events of the logic restricted to the parent interface. -/
private theorem handle_events (x : Input P (Msg L C) (Timer L C) I.Req) (s : State L C) :
    stepEvents (x, (handle L C p now x s).2.flatMap (externalOutputs L C)) =
      (handle L C p now x s).2.flatMap
        (fun e => e.getLeft?.toList.flatMap fun a => (stepEvents a).filterMap Event.parent?) := by
  rw [stepEvents, List.filterMap_flatMap]
  rcases h : dispatch L C x with y | ⟨j, y⟩ <;> simp only [handle, h]
  · rw [(logicIn_events y s).1, (logicIn_events y s).2, stepEvents, List.filterMap_append]
    congr 1
    rcases x with _ | ⟨_, _ | ⟨_, _⟩⟩ | (_ | ⟨_, _⟩) <;> cases h <;> rfl
  · have hx : x.req? = none := by
      rcases x with _ | ⟨_, _ | ⟨_, _⟩⟩ | (_ | ⟨_, _⟩) <;> cases h <;> rfl
    simp only [hx, Option.map_none, Option.toList_none, List.nil_append, childIn, childStep,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      filterMap_externalOutputs_inr, Sum.getLeft?_inr, Option.toList_none, List.flatMap_nil]
    refine flatMap_foldSteps_eq (fun o _ s => ?_) _
    rcases o with _ | x | _
    · rfl
    · simp only [routeChild]
      rw [(logicIn_events _ s).1, (logicIn_events _ s).2, stepEvents, List.filterMap_append]
      rfl
    · rfl

/-! #### External outputs -/

omit [DecidableEq ι] in
private theorem mem_externalOutputs_logic {o : L.Out} {o' : Output P (Msg L C) (Timer L C) I.Ind}
    (h₁ : ∀ o₁, liftLogic L C o₁ = some o' ↔ o₁ = o) (h₂ : ∀ j o₁, liftChild L C j o₁ ≠ some o')
    (e : Entry L C) : o' ∈ externalOutputs L C e ↔ ∃ a, e.getLeft? = some a ∧ o ∈ a.2 := by
  rcases e with ⟨y, os⟩ | ⟨j, y, os⟩ <;> simp [externalOutputs, h₁, h₂]

private theorem mem_externalOutputs_child {i : ι} {o : (C i).Out}
    {o' : Output P (Msg L C) (Timer L C) I.Ind}
    (h₁ : ∀ j o₁, liftChild L C j o₁ = some o' ↔ (⟨j, o₁⟩ : Σ j, (C j).Out) = ⟨i, o⟩)
    (h₂ : ∀ o₁, liftLogic L C o₁ ≠ some o') (e : Entry L C) :
    o' ∈ externalOutputs L C e ↔ ∃ a, rightGet? i e = some a ∧ o ∈ a.2 := by
  rcases e with ⟨y, os⟩ | ⟨j, y, os⟩
  · simp [externalOutputs, h₂]
  · by_cases h : j = i
    · subst h
      simp [externalOutputs, h₁]
    · simp [externalOutputs, h₁, sigmaGet?_mk_of_ne h, h]

end Compose

/-- The composite of a parent-request-quiet logic is request-quiet. (Indications that children
emit while handling requests are never routed, so no assumption on the children is needed.) -/
theorem Protocol.requestQuiet_compose {L : Protocol P (I.uses J)} {C : (i : ι) → Protocol P (J i)}
    (hL : L.ParentRequestQuiet) : (L.compose C).RequestQuiet := by
  intro p now r s i hi
  have h : Event.ind i ∈ ((Compose.logicIn L C p now (.req (.inl r)) s).2.flatMap
      (Compose.externalOutputs L C)).filterMap fun o => o.ind?.map Event.ind :=
    List.mem_filterMap.2 ⟨_, hi, rfl⟩
  rw [List.filterMap_flatMap, (Compose.logicIn_events _ s).1] at h
  obtain ⟨_, h, he⟩ := List.mem_filterMap.1 h
  obtain ⟨o, ho, ho'⟩ := List.mem_filterMap.1 h
  rcases o with _ | (_ | _) | _ <;> cases ho' <;> cases he
  exact hL p now r s.1 i ho

/-! ### Projections of runs of the composite -/

namespace Run

variable {L : Protocol P (I.uses J)} {C : (i : ι) → Protocol P (J i)} (ρ : Run (L.compose C))

/-- The component steps taken while `p` handles its inputs at time `τ`, in order. -/
def entries (p : P) (τ : ℕ) : List (Compose.Entry L C) :=
  (foldSteps (Compose.handle L C p (ρ.clock p τ)) (ρ.input p τ) (ρ.state p τ)).2

/-- The projection of a run of the composite onto the logic. -/
@[simps faulty gst clock]
def logic : Run L where
  faulty := ρ.faulty
  gst := ρ.gst
  clock := ρ.clock
  input p τ := ((ρ.entries p τ).filterMap Sum.getLeft?).map Prod.fst

/-- The projection of a run of the composite onto child `i`. -/
@[simps faulty gst clock]
def child (i : ι) : Run (C i) where
  faulty := ρ.faulty
  gst := ρ.gst
  clock := ρ.clock
  input p τ := ((ρ.entries p τ).filterMap (rightGet? i)).map Prod.fst

variable {ρ}

private theorem fst_state (p : P) (τ : ℕ) : (ρ.state p τ).1 = ρ.logic.state p τ := by
  induction τ with
  | zero => rfl
  | succ τ ih =>
    rw [state_succ, state_succ, Compose.batch_compose_fst, ← ih]
    exact (congrArg Prod.fst (Compose.sim_logic (ρ.input p τ) (ρ.state p τ))).symm

private theorem snd_state (i : ι) (p : P) (τ : ℕ) :
    (ρ.state p τ).2 i = (ρ.child i).state p τ := by
  induction τ with
  | zero => rfl
  | succ τ ih =>
    rw [state_succ, state_succ, Compose.batch_compose_fst, ← ih]
    exact (congrArg Prod.fst (Compose.sim_child i (ρ.input p τ) (ρ.state p τ))).symm

/-- The state of the composite consists of the states of the projections. -/
theorem state_compose (p : P) (τ : ℕ) :
    ρ.state p τ = (ρ.logic.state p τ, fun i => (ρ.child i).state p τ) :=
  Prod.ext (fst_state p τ) (funext fun i => snd_state i p τ)

/-- The steps of the logic projection are the logic steps of the composite. -/
theorem steps_logic (p : P) (τ : ℕ) :
    ρ.logic.steps p τ = (ρ.entries p τ).filterMap Sum.getLeft? := by
  rw [Run.steps, ← fst_state]
  exact congrArg Prod.snd (Compose.sim_logic (ρ.input p τ) (ρ.state p τ))

/-- The steps of a child projection are the steps of that child in the composite. -/
theorem steps_child (i : ι) (p : P) (τ : ℕ) :
    (ρ.child i).steps p τ = (ρ.entries p τ).filterMap (rightGet? i) := by
  rw [Run.steps, ← snd_state]
  exact congrArg Prod.snd (Compose.sim_child i (ρ.input p τ) (ρ.state p τ))

/-- The outputs of the composite are the external outputs of the component steps. -/
theorem output_compose (p : P) (τ : ℕ) :
    ρ.output p τ = (ρ.entries p τ).flatMap (Compose.externalOutputs L C) :=
  Compose.flatMap_batch_compose (G := Prod.snd) (fun _ _ => rfl) _ _

/-! #### Network and timer events of the projections -/

section lists

variable {α β γ δ : Type*}

private theorem filterMap_map_filterMap (π : α → Option (β × γ)) (F : β → Option δ)
    (l : List α) : ((l.filterMap π).map Prod.fst).filterMap F =
      l.flatMap fun e => ((π e).bind fun a => F a.1).toList := by
  rw [List.filterMap_map, List.filterMap_filterMap, List.filterMap_eq_flatMap_toList]
  rfl

private theorem flatMap_filterMap (π : α → Option β) (G : β → List γ) (l : List α) :
    (l.filterMap π).flatMap G = l.flatMap fun e => (π e).toList.flatMap G := by
  rw [List.filterMap_eq_flatMap_toList, List.flatMap_assoc]

end lists

private theorem input_logic_nonReq (p : P) (τ : ℕ) :
    (ρ.logic.input p τ).filterMap Compose.nonReq? =
      (ρ.input p τ).flatMap fun x => ((Compose.netIn (Compose.dispatch L C x)).bind
        Sum.getLeft?).toList := by
  have : ∀ x : (L.compose C).In, ((Compose.netIn (Compose.dispatch L C x)).bind
      Sum.getLeft?).toList = (Compose.netIn (Compose.dispatch L C x)).toList.flatMap
        fun z => z.getLeft?.toList := fun x => by
    cases Compose.netIn (Compose.dispatch L C x) <;> simp
  simp only [this, ← List.flatMap_assoc]
  rw [← flatMap_foldSteps (fun x _ s => Compose.handle_netIn x s) (ρ.state p τ),
    List.flatMap_assoc]
  refine (filterMap_map_filterMap _ _ _).trans (List.flatMap_congr fun e _ => ?_)
  rcases e with ⟨y, os⟩ | ⟨j, y, os⟩
  · cases y <;> rfl
  · cases y <;> rfl

private theorem input_child_nonReq (i : ι) (p : P) (τ : ℕ) :
    ((ρ.child i).input p τ).filterMap Compose.nonReq? =
      (ρ.input p τ).flatMap fun x => ((Compose.netIn (Compose.dispatch L C x)).bind
        (rightGet? i)).toList := by
  have : ∀ x : (L.compose C).In, ((Compose.netIn (Compose.dispatch L C x)).bind
      (rightGet? i)).toList = (Compose.netIn (Compose.dispatch L C x)).toList.flatMap
        fun z => (rightGet? i z).toList := fun x => by
    cases Compose.netIn (Compose.dispatch L C x) <;> simp
  simp only [this, ← List.flatMap_assoc]
  rw [← flatMap_foldSteps (fun x _ s => Compose.handle_netIn x s) (ρ.state p τ),
    List.flatMap_assoc]
  refine (filterMap_map_filterMap _ _ _).trans (List.flatMap_congr fun e _ => ?_)
  rcases e with ⟨y, os⟩ | ⟨j, y, os⟩
  · cases y <;> rfl
  · by_cases h : j = i
    · subst h
      cases y <;> simp [Compose.netIn, Compose.entryInput, Compose.nonReq?]
    · cases y <;> simp [Compose.netIn, Compose.entryInput, Compose.nonReq?, sigmaGet?_mk_of_ne h]

private theorem mem_input_logic_iff {p : P} {τ : ℕ} {z : L.In} (hz : z.req? = none) :
    z ∈ ρ.logic.input p τ ↔
      ∃ x ∈ ρ.input p τ, (Compose.netIn (Compose.dispatch L C x)).bind Sum.getLeft? = some z := by
  have : z ∈ ρ.logic.input p τ ↔ z ∈ (ρ.logic.input p τ).filterMap Compose.nonReq? := by
    simp [List.mem_filterMap, Compose.nonReq?_eq_some_iff, hz]
  rw [this, input_logic_nonReq]
  simp

private theorem mem_input_child_iff {i : ι} {p : P} {τ : ℕ} {z : (C i).In} (hz : z.req? = none) :
    z ∈ (ρ.child i).input p τ ↔
      ∃ x ∈ ρ.input p τ, (Compose.netIn (Compose.dispatch L C x)).bind (rightGet? i) = some z := by
  have : z ∈ (ρ.child i).input p τ ↔
      z ∈ ((ρ.child i).input p τ).filterMap Compose.nonReq? := by
    simp [List.mem_filterMap, Compose.nonReq?_eq_some_iff, hz]
  rw [this, input_child_nonReq]
  simp

private theorem mem_output_logic_iff {o : L.Out} {o' : (L.compose C).Out}
    (h₁ : ∀ o₁, Compose.liftLogic L C o₁ = some o' ↔ o₁ = o)
    (h₂ : ∀ j o₁, Compose.liftChild L C j o₁ ≠ some o') {p : P} {τ : ℕ} :
    o ∈ ρ.logic.output p τ ↔ o' ∈ ρ.output p τ := by
  rw [output_compose, Run.output, steps_logic]
  simp only [List.mem_flatMap, List.mem_filterMap, Compose.mem_externalOutputs_logic h₁ h₂]
  constructor
  · rintro ⟨a, ⟨e, he, hea⟩, ho⟩
    exact ⟨e, he, a, hea, ho⟩
  · rintro ⟨e, he, a, hea, ho⟩
    exact ⟨a, ⟨e, he, hea⟩, ho⟩

private theorem mem_output_child_iff {i : ι} {o : (C i).Out} {o' : (L.compose C).Out}
    (h₁ : ∀ j o₁, Compose.liftChild L C j o₁ = some o' ↔ (⟨j, o₁⟩ : Σ j, (C j).Out) = ⟨i, o⟩)
    (h₂ : ∀ o₁, Compose.liftLogic L C o₁ ≠ some o') {p : P} {τ : ℕ} :
    o ∈ (ρ.child i).output p τ ↔ o' ∈ ρ.output p τ := by
  rw [output_compose, Run.output, steps_child]
  simp only [List.mem_flatMap, List.mem_filterMap, Compose.mem_externalOutputs_child h₁ h₂]
  constructor
  · rintro ⟨a, ⟨e, he, hea⟩, ho⟩
    exact ⟨e, he, a, hea, ho⟩
  · rintro ⟨e, he, a, hea, ho⟩
    exact ⟨a, ⟨e, he, hea⟩, ho⟩

/-- The logic receives exactly the logic messages received by the composite. -/
theorem recv_mem_input_logic {p q : P} {τ : ℕ} {m : L.Msg} :
    .recv q m ∈ ρ.logic.input p τ ↔ .recv q (.inl m) ∈ ρ.input p τ := by
  have key : ∀ x, (Compose.netIn (Compose.dispatch L C x)).bind Sum.getLeft? =
      some (.recv q m) ↔ x = .recv q (.inl m) := by
    intro x
    rcases x with _ | ⟨_, _ | ⟨_, _⟩⟩ | (_ | ⟨_, _⟩) <;>
      simp [Compose.dispatch, Compose.netIn, Compose.nonReq?, eq_comm]
  rw [mem_input_logic_iff rfl]
  simp [key]

/-- The timers of the logic expire exactly when the corresponding timers of the composite do. -/
theorem timeout_mem_input_logic {p : P} {τ : ℕ} {k : L.Timer} :
    .timeout k ∈ ρ.logic.input p τ ↔ .timeout (.inl k) ∈ ρ.input p τ := by
  have key : ∀ x, (Compose.netIn (Compose.dispatch L C x)).bind Sum.getLeft? =
      some (.timeout k) ↔ x = .timeout (.inl k) := by
    intro x
    rcases x with _ | ⟨_, _ | ⟨_, _⟩⟩ | (_ | ⟨_, _⟩) <;>
      simp [Compose.dispatch, Compose.netIn, Compose.nonReq?, eq_comm]
  rw [mem_input_logic_iff rfl]
  simp [key]

/-- The logic sends exactly the logic messages sent by the composite. -/
theorem send_mem_output_logic {p q : P} {τ : ℕ} {m : L.Msg} :
    .send q m ∈ ρ.logic.output p τ ↔ .send q (.inl m) ∈ ρ.output p τ :=
  mem_output_logic_iff
    (fun o => by rcases o with _ | (_ | _) | _ <;> simp [Compose.liftLogic])
    (fun _ o => by rcases o with _ | _ | _ <;> simp [Compose.liftChild])

/-- The logic sets exactly the logic timers set by the composite. -/
theorem setTimer_mem_output_logic {p : P} {τ T : ℕ} {k : L.Timer} :
    .setTimer k T ∈ ρ.logic.output p τ ↔ .setTimer (.inl k) T ∈ ρ.output p τ :=
  mem_output_logic_iff
    (fun o => by rcases o with _ | (_ | _) | _ <;> simp [Compose.liftLogic])
    (fun _ o => by rcases o with _ | _ | _ <;> simp [Compose.liftChild])

/-- Child `i` receives exactly the messages of child `i` received by the composite. -/
theorem recv_mem_input_child {i : ι} {p q : P} {τ : ℕ} {m : (C i).Msg} :
    .recv q m ∈ (ρ.child i).input p τ ↔ .recv q (.inr ⟨i, m⟩) ∈ ρ.input p τ := by
  have key : ∀ x, (Compose.netIn (Compose.dispatch L C x)).bind (rightGet? i) =
      some (.recv q m) ↔ x = .recv q (.inr ⟨i, m⟩) := by
    intro x
    rcases x with _ | ⟨_, _ | ⟨j, _⟩⟩ | (_ | ⟨j, _⟩)
    all_goals try by_cases h : j = i
    all_goals try subst h
    all_goals simp [Compose.dispatch, Compose.netIn, Compose.nonReq?, *]
  rw [mem_input_child_iff rfl]
  simp [key]

/-- The timers of child `i` expire exactly when the corresponding timers of the composite do. -/
theorem timeout_mem_input_child {i : ι} {p : P} {τ : ℕ} {k : (C i).Timer} :
    .timeout k ∈ (ρ.child i).input p τ ↔ .timeout (.inr ⟨i, k⟩) ∈ ρ.input p τ := by
  have key : ∀ x, (Compose.netIn (Compose.dispatch L C x)).bind (rightGet? i) =
      some (.timeout k) ↔ x = .timeout (.inr ⟨i, k⟩) := by
    intro x
    rcases x with _ | ⟨_, _ | ⟨j, _⟩⟩ | (_ | ⟨j, _⟩)
    all_goals try by_cases h : j = i
    all_goals try subst h
    all_goals simp [Compose.dispatch, Compose.netIn, Compose.nonReq?, *]
  rw [mem_input_child_iff rfl]
  simp [key]

/-- Child `i` sends exactly the messages of child `i` sent by the composite. -/
theorem send_mem_output_child {i : ι} {p q : P} {τ : ℕ} {m : (C i).Msg} :
    .send q m ∈ (ρ.child i).output p τ ↔ .send q (.inr ⟨i, m⟩) ∈ ρ.output p τ :=
  mem_output_child_iff
    (fun j o => by
      by_cases h : j = i
      · subst h
        rcases o with _ | _ | _ <;> simp [Compose.liftChild]
      · rcases o with _ | _ | _ <;> simp [Compose.liftChild, h])
    (fun o => by rcases o with _ | (_ | _) | _ <;> simp [Compose.liftLogic])

/-- Child `i` sets exactly the timers of child `i` set by the composite. -/
theorem setTimer_mem_output_child {i : ι} {p : P} {τ T : ℕ} {k : (C i).Timer} :
    .setTimer k T ∈ (ρ.child i).output p τ ↔ .setTimer (.inr ⟨i, k⟩) T ∈ ρ.output p τ :=
  mem_output_child_iff
    (fun j o => by
      by_cases h : j = i
      · subst h
        rcases o with _ | _ | _ <;> simp [Compose.liftChild]
      · rcases o with _ | _ | _ <;> simp [Compose.liftChild, h])
    (fun o => by rcases o with _ | (_ | _) | _ <;> simp [Compose.liftLogic])

/-! #### The projection theorem -/

variable {t δ : ℕ}

/-- The projection of a valid run of the composite onto the logic is a valid run. -/
theorem Valid.logic (hρ : ρ.Valid t δ) : ρ.logic.Valid t δ where
  card_faulty_le := hρ.card_faulty_le
  clock_mono := hρ.clock_mono
  clock_succ := hρ.clock_succ
  authentic hp hq h := by
    obtain ⟨τ', hτ', h', hd⟩ := hρ.authentic hp hq (recv_mem_input_logic.1 h)
    exact ⟨τ', hτ', send_mem_output_logic.2 h', hd⟩
  reliable hp hq h := by
    obtain ⟨τ', h₁, h₂, h'⟩ := hρ.reliable hp hq (send_mem_output_logic.1 h)
    exact ⟨τ', h₁, h₂, recv_mem_input_logic.2 h'⟩
  timer hp := by
    rw [timeout_mem_input_logic, hρ.timer hp]
    exact exists_congr fun _ => exists_congr fun _ => and_congr setTimer_mem_output_logic.symm .rfl

/-- The projection of a valid run of the composite onto a child is a valid run. -/
theorem Valid.child (hρ : ρ.Valid t δ) (i : ι) : (ρ.child i).Valid t δ where
  card_faulty_le := hρ.card_faulty_le
  clock_mono := hρ.clock_mono
  clock_succ := hρ.clock_succ
  authentic hp hq h := by
    obtain ⟨τ', hτ', h', hd⟩ := hρ.authentic hp hq (recv_mem_input_child.1 h)
    exact ⟨τ', hτ', send_mem_output_child.2 h', hd⟩
  reliable hp hq h := by
    obtain ⟨τ', h₁, h₂, h'⟩ := hρ.reliable hp hq (send_mem_output_child.1 h)
    exact ⟨τ', h₁, h₂, recv_mem_input_child.2 h'⟩
  timer hp := by
    rw [timeout_mem_input_child, hρ.timer hp]
    exact exists_congr fun _ => exists_congr fun _ => and_congr setTimer_mem_output_child.symm .rfl

/-- The requests handled by child `i` are the requests to `i` emitted by the logic, in order. -/
theorem child_reqs (i : ι) (p : P) (τ : ℕ) :
    ((ρ.child i).input p τ).filterMap Input.req? =
      (ρ.logic.output p τ).filterMap fun o => o.ind?.bind (rightGet? i) := by
  rw [Run.output, steps_logic, List.filterMap_flatMap, flatMap_filterMap]
  change (((ρ.entries p τ).filterMap (rightGet? i)).map Prod.fst).filterMap Input.req? = _
  rw [filterMap_map_filterMap]
  exact flatMap_foldSteps_eq (fun x _ s => Compose.handle_reqs i x s) _

/-- If child `i` is request-quiet, the indications of child `i` are the indications from `i`
handled by the logic, in order. -/
theorem child_inds (i : ι) (hC : (C i).RequestQuiet) (p : P) (τ : ℕ) :
    ((ρ.child i).output p τ).filterMap Output.ind? =
      (ρ.logic.input p τ).filterMap fun y => y.req?.bind (rightGet? i) := by
  rw [Run.output, steps_child, List.filterMap_flatMap, flatMap_filterMap]
  change _ = (((ρ.entries p τ).filterMap Sum.getLeft?).map Prod.fst).filterMap _
  rw [filterMap_map_filterMap]
  exact flatMap_foldSteps_eq (fun x _ s => Compose.handle_inds i hC x s) _

/-- Child `i` handles request `r` at `τ` iff the logic emits the request `r` to `i` at `τ`. -/
theorem req_mem_input_child {i : ι} {p : P} {τ : ℕ} {r : (J i).Req} :
    .req r ∈ (ρ.child i).input p τ ↔ .ind (.inr ⟨i, r⟩) ∈ ρ.logic.output p τ := by
  have := congrArg (r ∈ ·) (child_reqs (ρ := ρ) i p τ)
  simpa [Option.bind_eq_some_iff] using this

/-- *At most once, for child requests.* If the logic emits at most one request to child `i` of a
certain kind (more precisely, at most one event of a kind `b'` that includes the requests
`r` to `i` with `b (.req r)`), then child `i` handles at most one request of kind `b`. This
transfers the environment assumptions "at most one request of kind `b`" of the children's
specifications. -/
theorem atMostOnce_child_of_logic {i : ι} {p : P} {b : Event (J i) → Bool}
    {b' : Event (I.uses J) → Bool} (hb : ∀ x, b (.ind x) = false)
    (hb' : ∀ r, b (.req r) = true → b' (.ind (.inr ⟨i, r⟩)) = true)
    (h : ρ.logic.history.AtMostOnce p b') : (ρ.child i).history.AtMostOnce p b := by
  refine h.of_countP_trace_le fun τ => ?_
  simp only [history_trace]
  rw [Event.countP_eq_countP_filterMap_req? hb, filterMap_req?_trace, child_reqs,
    ← List.filterMap_filterMap]
  refine le_trans ?_ (Event.countP_filterMap_ind?_le b' _)
  rw [filterMap_ind?_trace, List.countP_filterMap]
  refine List.countP_mono_left fun e _ he => ?_
  rcases e with e | ⟨j, r⟩
  · simp [rightGet?] at he
  · by_cases hj : j = i
    · subst hj
      simp only [rightGet?_inr, sigmaGet?_mk, Option.map_some, Option.getD_some] at he
      exact hb' r he
    · simp [rightGet?, sigmaGet?_mk_of_ne hj] at he

/-- If child `i` is request-quiet, it emits indication `x` at `τ` iff the logic handles `x` as an
indication from `i` at `τ`. -/
theorem ind_mem_output_child {i : ι} (hC : (C i).RequestQuiet) {p : P} {τ : ℕ} {x : (J i).Ind} :
    .ind x ∈ (ρ.child i).output p τ ↔ .req (.inr ⟨i, x⟩) ∈ ρ.logic.input p τ := by
  have := congrArg (x ∈ ·) (child_inds (ρ := ρ) i hC p τ)
  simpa [Option.bind_eq_some_iff] using this

/-- The trace of the composite is the trace of the logic restricted to the parent interface. -/
theorem trace_compose (p : P) (τ : ℕ) :
    ρ.trace p τ = (ρ.logic.trace p τ).filterMap Event.parent? := by
  rw [Run.trace, Run.trace, steps_logic, List.filterMap_flatMap, flatMap_filterMap]
  exact Compose.flatMap_batch_compose (fun x s => Compose.handle_events x s) _ _

/-! #### Histories of the composite and of the children

The events of the history of the composite and of the children in terms of the inputs and
outputs of the logic: the form in which specifications of the composite and of the children meet
the reasoning about the logic. -/

/-- The composite handles request `r` of the parent interface at `τ` iff the logic does. -/
theorem history_reqAt_compose {p : P} {τ : ℕ} {r : I.Req} :
    ρ.history.ReqAt p r τ ↔ .req (.inl r) ∈ ρ.logic.input p τ := by
  rw [History.ReqAt, history_trace, trace_compose, List.mem_filterMap, ← req_mem_trace]
  constructor
  · rintro ⟨e, he, h⟩
    rcases e with (_ | _) | (_ | _) <;> cases h
    exact he
  · exact fun h => ⟨_, h, rfl⟩

/-- The composite emits indication `i` of the parent interface at `τ` iff the logic does. -/
theorem history_indAt_compose {p : P} {τ : ℕ} {i : I.Ind} :
    ρ.history.IndAt p i τ ↔ .ind (.inl i) ∈ ρ.logic.output p τ := by
  rw [History.IndAt, history_trace, trace_compose, List.mem_filterMap, ← ind_mem_trace]
  constructor
  · rintro ⟨e, he, h⟩
    rcases e with (_ | _) | (_ | _) <;> cases h
    exact he
  · exact fun h => ⟨_, h, rfl⟩

/-- Child `i` handles request `r` at `τ` iff the logic emits the request `r` to `i` at `τ`. -/
theorem history_reqAt_child {i : ι} {p : P} {τ : ℕ} {r : (J i).Req} :
    (ρ.child i).history.ReqAt p r τ ↔ .ind (.inr ⟨i, r⟩) ∈ ρ.logic.output p τ :=
  history_reqAt.trans req_mem_input_child

/-- If child `i` is request-quiet, it emits indication `x` at `τ` iff the logic handles `x` as an
indication from `i` at `τ`. -/
theorem history_indAt_child {i : ι} (hC : (C i).RequestQuiet) {p : P} {τ : ℕ} {x : (J i).Ind} :
    (ρ.child i).history.IndAt p x τ ↔ .req (.inr ⟨i, x⟩) ∈ ρ.logic.input p τ :=
  history_indAt.trans (ind_mem_output_child hC)

/-- Specifications satisfied by a child hold for its projection in a valid run of the
composite. -/
theorem Valid.satisfies_child (hρ : ρ.Valid t δ) {i : ι} {S : Spec P (J i)}
    (hS : (C i).Satisfies t δ S) : S (ρ.child i).history :=
  hS _ (hρ.child i)

end Run

end Cslib.Distributed
