/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Computability.Distributed.Byzantine.LockStep.Auth

/-!
# Running a protocol among a committee

Many synchronous protocols contain a step "the parties of a subset `C` run protocol `alg` among
themselves" (e.g. a black-box agreement protocol among the registered / unregistered parties of a
partially authenticated system). Here `alg : Protocol C I M O` is a protocol whose parties are the
members of `C : Set P`, and

* `alg.extend C : Protocol P I M O` runs it inside `P`: members of `C` send to members of `C` as
  in `alg` (ignoring messages from non-members), non-members send nothing and never decide;
* `s.restrict C : Scenario C I M` is the induced scenario among `C` (Byzantine members of `C`,
  their messages to members, omissions between members).

`restrictHist_hist_extend` identifies the run of `alg.extend C` (seen by members, restricted to
member senders) with the run of `alg` in `s.restrict C`, on any graph `G'` on `C` with the
adjacency induced by `G`. Decisions transfer (`decides_extend_iff`), and so does the authenticated
setting (with the lifted signature structure `Cslib.Byzantine.Auth.extend`:
`Protocol.Unforging.extend`, `Scenario.AuthValid.restrict`).
-/

@[expose] public section

namespace Cslib.Byzantine.LockStep

variable {P I M O S : Type*} (C : Set P)

/-! ### Restricting inboxes and histories -/

/-- The messages from members of `C`. -/
def restrictInbox (ib : Inbox P M) : Inbox C M := fun q => ib q

/-- A history, restricted to the messages from members of `C`. -/
def restrictHist (h : History P M) : History C M := h.map (restrictInbox C)

/-- Restricting a history keeps its length. -/
@[simp] lemma length_restrictHist (h : History P M) : (restrictHist C h).length = h.length :=
  List.length_map _

/-- Restriction commutes with appending histories. -/
@[simp] lemma restrictHist_append (h₁ h₂ : History P M) :
    restrictHist C (h₁ ++ h₂) = restrictHist C h₁ ++ restrictHist C h₂ := List.map_append

/-! ### The protocol and the scenario -/

open Classical in
/-- Run the committee protocol `alg` inside `P`: members of `C` talk to members of `C` as in `alg`
(only messages from members are passed on); non-members are silent and never decide. -/
noncomputable def Protocol.extend (alg : Protocol C I M O) : Protocol P I M O where
  send p x h q :=
    if hp : p ∈ C then
      if hq : q ∈ C then alg.send ⟨p, hp⟩ x (restrictHist C h) ⟨q, hq⟩ else none
    else none
  decide p x h := if hp : p ∈ C then alg.decide ⟨p, hp⟩ x (restrictHist C h) else none

/-- The scenario induced among the members of `C`. -/
def Scenario.restrict (s : Scenario P I M) : Scenario C I M where
  byz := {q | q.1 ∈ s.byz}
  input q := s.input q
  adv r b q := s.adv r b q
  drop r b q := s.drop r b q

variable {C}

/-- Between members, the extended protocol sends what `alg` sends on the restricted history. -/
lemma Protocol.extend_send_of_mem (alg : Protocol C I M O) {p q : P} (hp : p ∈ C) (hq : q ∈ C)
    (x : I) (h : History P M) :
    (alg.extend C).send p x h q = alg.send ⟨p, hp⟩ x (restrictHist C h) ⟨q, hq⟩ := by
  simp [Protocol.extend, hp, hq]

/-- A member decides as in `alg` on the restricted history. -/
lemma Protocol.extend_decide_of_mem (alg : Protocol C I M O) {p : P} (hp : p ∈ C) (x : I)
    (h : History P M) : (alg.extend C).decide p x h = alg.decide ⟨p, hp⟩ x (restrictHist C h) := by
  simp [Protocol.extend, hp]

/-- A message of the extended protocol is a message of `alg` between members. -/
lemma Protocol.exists_of_extend_send {alg : Protocol C I M O} {p q : P} {x : I}
    {h : History P M} {m : M} (hm : (alg.extend C).send p x h q = some m) :
    ∃ (hp : p ∈ C) (hq : q ∈ C), alg.send ⟨p, hp⟩ x (restrictHist C h) ⟨q, hq⟩ = some m := by
  simp only [Protocol.extend] at hm
  split_ifs at hm with hp hq
  exact ⟨hp, hq, hm⟩

section Simp
variable (s : Scenario P I M)
/-- The Byzantine members are the members that are Byzantine in `s`. -/
@[simp] lemma Scenario.mem_restrict_byz {q : C} : q ∈ (s.restrict C).byz ↔ q.1 ∈ s.byz := Iff.rfl
/-- Members keep their inputs. -/
@[simp] lemma Scenario.restrict_input (q : C) : (s.restrict C).input q = s.input q := rfl
/-- Byzantine members send what they send in `s`. -/
@[simp] lemma Scenario.restrict_adv (r : ℕ) (b q : C) : (s.restrict C).adv r b q = s.adv r b q :=
  rfl
/-- Omissions between members are those of `s`. -/
@[simp] lemma Scenario.restrict_drop (r : ℕ) (b q : C) :
    (s.restrict C).drop r b q = s.drop r b q := rfl
end Simp

/-! ### Runs -/

variable {G : SimpleGraph P} {G' : SimpleGraph C} (hG : ∀ p q : C, G'.Adj p q ↔ G.Adj p q)
  (alg : Protocol C I M O) (s : Scenario P I M)
include hG

/-- **Simulation lemma**: the run of `alg.extend C`, seen by a member and restricted to member
senders, is the run of `alg` in the induced scenario. -/
theorem restrictHist_hist_extend (r : ℕ) (p : C) :
    restrictHist C (hist G (alg.extend C) s r p) = hist G' alg (s.restrict C) r p := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    rw [hist_succ, hist_succ, restrictHist_append, ih]
    congr 1
    simp only [restrictHist, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    funext q
    simp only [restrictInbox, deliver]
    by_cases hadj : G'.Adj q p
    · have hadj' := (hG q p).1 hadj
      by_cases hb : q.1 ∈ s.byz
      · simp [hadj, hadj', hb]
      · by_cases hd : s.drop r q p
        · simp [hadj, hadj', hb, hd]
        · have hb' : q ∉ (s.restrict C).byz := hb
          have hd' : ¬ (s.restrict C).drop r q p := hd
          simp only [hadj, hadj', hb, hb', hd, hd', ↓reduceIte,
            Protocol.extend_send_of_mem alg q.2 p.2, ih q]
          rfl
    · have hadj' : ¬ G.Adj q p := fun h => hadj ((hG q p).2 h)
      simp [hadj, hadj']

/-- A member's decision status in the extended protocol is its status in the induced run. -/
lemma status_extend (r : ℕ) (p : C) :
    status G (alg.extend C) s r p = status G' alg (s.restrict C) r p := by
  simp only [status, Protocol.extend_decide_of_mem alg p.2, restrictHist_hist_extend hG]
  rfl

/-- A member decides in the extended protocol what it decides in the induced run. -/
lemma decides_extend_iff (p : C) (o : O) :
    Decides G (alg.extend C) s p o ↔ Decides G' alg (s.restrict C) p o := by
  simp only [decides_iff_firstSome, status_extend hG]

/-! ### The authenticated setting -/

omit hG

/-- Tokens of a restricted history occur in the full history. -/
lemma Auth.histTokens_extend (A : Auth C M S) {h : History P M} {τ : S}
    (hτ : τ ∈ A.histTokens (restrictHist C h)) : τ ∈ Auth.histTokens A.extend h := by
  obtain ⟨ib, hib, q, m, hm, hτm⟩ := hτ
  obtain ⟨ib', hib', rfl⟩ := List.mem_map.1 hib
  exact ⟨ib', hib', q.1, m, hm, hτm⟩

/-- The extended protocol is unforging for the lifted signature structure. -/
lemma Protocol.Unforging.extend {A : Auth C M S} {alg : Protocol C I M O} (hU : alg.Unforging A) :
    (alg.extend C).Unforging A.extend := by
  intro p x h q m hm τ hτ
  obtain ⟨hp, hq, hm'⟩ := Protocol.exists_of_extend_send hm
  rcases hU _ _ _ _ _ hm' τ hτ with h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (A.histTokens_extend h1)

include hG in
/-- An adversary respecting unforgeability in the extended protocol respects it in the induced
run. -/
lemma Scenario.AuthValid.restrict {A : Auth C M S} {s : Scenario P I M}
    (hV : s.AuthValid G (alg.extend C) A.extend) : (s.restrict C).AuthValid G' alg A := by
  intro r b q m hb hq hadj hm τ hτ
  rcases hV r b q m hb hq ((hG b q).1 hadj) hm τ hτ with
    h | ⟨r', hr', p, hp, q', hadj', m', hm', hτ'⟩
  · exact Or.inl h
  · right
    obtain ⟨hpC, hqC, hm''⟩ := Protocol.exists_of_extend_send hm'
    refine ⟨r', hr', ⟨p, hpC⟩, hp, ⟨q', hqC⟩, (hG _ _).2 hadj', m', ?_, hτ'⟩
    rw [← restrictHist_hist_extend hG]
    exact hm''

end Cslib.Byzantine.LockStep
