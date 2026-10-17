/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Data.Set.CoeSort

/-!
# Abstract signature structures

Ideal unforgeable signatures are modelled abstractly by *tokens*: every message `m : M` carries a
set of tokens `A.tokens m : Set K`, and every token `x : K` has a signer `A.signer x : P`. What a
token "says" is up to the concrete message type; tokens are opaque here. Unforgeability itself is
a restriction on algorithms and adversaries and is therefore model-specific.

This structure is shared by the Byzantine models of CSLib: `Cslib.Byzantine.LockStep.Auth` (the
synchronous lock-step model) and `Cslib.Byzantine.PartialSync.Auth` (the partially synchronous
model) are abbreviations of `Cslib.Byzantine.Auth`, and the model-specific notions (tokens of a
history, unforging protocols, unforgeability-respecting adversaries) live in the model namespaces.

Since dot notation resolves in the namespace of the head symbol of the type, a term whose type is
`Cslib.Byzantine.Auth …` (for instance `A.left`) does not see model-specific operations such as
`Cslib.Byzantine.LockStep.Auth.histTokens` through dot notation; use the full name for them.

## Main definitions

* `Auth.none`: the trivial structure (no tokens), i.e. the unauthenticated setting.
* `Auth.left`, `Auth.right`: the parts of a structure on sum messages `M₁ ⊕ M₂`.
* `Auth.extend`: a structure of a committee `C : Set P`, with signers seen as elements of `P`.
-/

@[expose] public section

namespace Cslib.Byzantine

/-- An abstract signature structure on messages: `P` signers, `M` messages, `K` tokens. -/
structure Auth (P M K : Type*) where
  /-- The signer of a token. -/
  signer : K → P
  /-- The signature tokens contained in a message. -/
  tokens : M → Set K

namespace Auth

variable {P M M₁ M₂ K : Type*}

/-- The trivial signature structure (no tokens): the unauthenticated setting. -/
def none (P M : Type*) : Auth P M Empty where
  signer := Empty.elim
  tokens _ := ∅

/-- The signature structure of the left messages of a structure on `M₁ ⊕ M₂`. -/
def left (A : Auth P (M₁ ⊕ M₂) K) : Auth P M₁ K where
  signer := A.signer
  tokens m := A.tokens (Sum.inl m)

/-- The signature structure of the right messages of a structure on `M₁ ⊕ M₂`. -/
def right (A : Auth P (M₁ ⊕ M₂) K) : Auth P M₂ K where
  signer := A.signer
  tokens m := A.tokens (Sum.inr m)

/-- A signature structure of the committee `C ⊆ P`, with signers seen as elements of `P`. -/
def extend {C : Set P} (A : Auth C M K) : Auth P M K where
  signer x := (A.signer x).1
  tokens := A.tokens

end Auth

end Cslib.Byzantine
