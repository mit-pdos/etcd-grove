/-
Package initialization of `k8s_io.client_go.util.retry`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True`. Its initializer allocates its variables (`util.go`: `DefaultRetry`,
`DefaultBackoff`, `wait.Backoff` literals), initializes its imports and runs the translated
initializers.
-/
module

public import Proof.k8s_io.client_go.Base
public import Perennial.Proof.time.Link
public import Proof.k8s_io.apimachinery.pkg.api.errors.Init
public import Proof.k8s_io.apimachinery.pkg.util.wait.Init

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
