/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/TimeoutNowRequest__GetRPCHeader.lean (241f27e).
-/
/-
`raft.(*TimeoutNowRequest).GetRPCHeader`'s spec (internal to the RPC handlers): returns the header field.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*TimeoutNowRequest).GetRPCHeader()`: the request's header. -/
abbrev github_com.hashicorp.raft.TimeoutNowRequest.GetRPCHeader.spec : Prop :=
  ∀ (p : Loc) (rq : TimeoutNowRequest),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ p ↦ rq }}
    (App (Val (p @!! go.GoType.PointerType TimeoutNowRequest.ty @!! go!"GetRPCHeader")) (Val #()))
  {{ RET #rq.RPCHeader'; p ↦ rq }}

end spec

end Perennial
