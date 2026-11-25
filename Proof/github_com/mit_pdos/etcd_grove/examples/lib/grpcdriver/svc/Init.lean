/-
Package initialization of `github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`drvDescs`, `svc/Base.lean`): its service descriptor `Driver_ServiceDesc`, read-only, with
its methods and streams exactly. Its initializer allocates and sets the descriptor (a `grpc.ServiceDesc`
literal) and initializes its imports.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.Base
public import Perennial.Proof.context.Link
public import Proof.google_golang_org.grpc.Init
public import Proof.google_golang_org.protobuf.types.known.wrapperspb.Init

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
