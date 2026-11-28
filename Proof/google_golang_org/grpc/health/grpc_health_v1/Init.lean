/-
Package initialization of `google_golang_org.grpc.health.grpc_health_v1`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`healthDescs`, `grpc_health_v1/Base.lean`): its service descriptor `Health_ServiceDesc`,
read-only, with its methods and stream exactly. Its initializer allocates and sets the descriptor (a
`grpc.ServiceDesc` literal, translated since 2026-11-26), initializes its imports and runs its `init`, whose
trusted model does nothing (`TrustedCode/google_golang_org/grpc/health/grpc_health_v1.lean`).
-/
module

public import Proof.google_golang_org.grpc.health.grpc_health_v1.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.strconv.Link
public import Proof.google_golang_org.grpc.Init

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
