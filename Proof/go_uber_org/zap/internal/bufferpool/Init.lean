/-
Package initialization of `go_uber_org.zap.internal.bufferpool`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True`. Its initializer allocates its variables, initializes `buffer` and runs their
translated initializers (zap-z1, 2026-11-23: zap's `Logger.check` reads `Get`): `_pool = buffer.NewPool()`
(`pool.New` of a function literal, proved) and `Get = _pool.Get` (a method value, not called).
-/
module

public import Proof.go_uber_org.zap.PkgInit
public import Proof.go_uber_org.zap.buffer.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

end Perennial
