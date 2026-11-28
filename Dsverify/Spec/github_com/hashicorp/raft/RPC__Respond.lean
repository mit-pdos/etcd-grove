/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/RPC__Respond.lean (241f27e).
-/
/-
`raft.(*RPC).Respond`'s spec (internal to the RPC handlers): sends the response on the RPC's response channel (a bag), giving it the response's resources.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Dsverify.Proof.github_com.hashicorp.raft.iface.Net

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

/-- `(*RPC).Respond(resp, err)`: sends `RPCResponse{resp, err}` on the bag `RespChan`. -/
abbrev github_com.hashicorp.raft.RPC.Respond.spec : Prop :=
  ∀ (p : Loc) (v : RPC) (γc : ChanNames) (P : RPCResponse → IProp GF)
    (resp err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ p ↦ v ∗
     isChanBag (V := RPCResponse) γc v.RespChan' P ∗ P (RPCResponse.mk resp err) }}
    (App (App (Val (p @!! go.GoType.PointerType RPC.ty @!! go!"Respond")) (Val #resp)) (Val #err))
  {{ RET #(); p ↦ v }}

end spec

end Perennial
