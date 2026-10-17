/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Cslib.Foundations.Data.Nat.Descent

/-! # "Eventually forever" for finitely many agents

If every agent eventually satisfies a property which, once true (after time `T0`), stays true, then
from some time on all agents satisfy it. This is the typical way to combine per-agent convergence
statements into a statement about whole configurations.

The statement is `Nat.eventually_forall_of_imp_succ` (in `Cslib.Foundations.Data.Nat.Descent`);
`Cslib.PopulationProtocol.eventually_all` is a deprecated alias of it.
-/

@[expose] public section

namespace Cslib.PopulationProtocol

@[deprecated (since := "2026-10-18")]
alias eventually_all := Nat.eventually_forall_of_imp_succ

end Cslib.PopulationProtocol
