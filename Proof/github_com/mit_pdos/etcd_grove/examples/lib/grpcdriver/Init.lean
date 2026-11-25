/-
Package initialization of `github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`drvFacts`, `Base.lean`): its variable `reached`, read-only, holds a function whose calls
return. Its initializer allocates `reached`, initializes its imports and stores `reached`'s function value.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.Init
public import Proof.google_golang_org.grpc.Init
public import Proof.google_golang_org.grpc.codes.Init
public import Proof.google_golang_org.grpc.credentials.insecure.Init
public import Proof.google_golang_org.grpc.metadata.Init
public import Proof.google_golang_org.grpc.status.Init
public import Proof.google_golang_org.protobuf.types.known.wrapperspb.Init
public import Proof.net.Init

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
