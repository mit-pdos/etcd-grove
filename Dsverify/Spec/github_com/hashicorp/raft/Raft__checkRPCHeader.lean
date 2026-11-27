/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__checkRPCHeader.lean (241f27e).
-/
/-
`raft.(*Raft).checkRPCHeader`'s spec (internal to the RPC handlers): a request of the program (protocol version 3) passes.
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

/-- `(*Raft).checkRPCHeader(rpc)`: the program's requests (of the three kinds, protocol version 3)
pass (`nil`). -/
abbrev github_com.hashicorp.raft.Raft.checkRPCHeader.spec : Prop :=
  (∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (rpc : RPC) (p : Loc) (rq : AppendEntriesRequest),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     ⌜rpc.Command' = interface.mkOk (go.GoType.PointerType AppendEntriesRequest.ty) #p ∧
       rq.RPCHeader'.ProtocolVersion' = W64 3⌝ ∗ p ↦ rq }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"checkRPCHeader")) (Val #rpc))
  {{ RET #interface.nil; p ↦ rq }}) ∧
  (∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (rpc : RPC) (p : Loc) (rq : RequestVoteRequest),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     ⌜rpc.Command' = interface.mkOk (go.GoType.PointerType RequestVoteRequest.ty) #p ∧
       rq.RPCHeader'.ProtocolVersion' = W64 3⌝ ∗ p ↦ rq }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"checkRPCHeader")) (Val #rpc))
  {{ RET #interface.nil; p ↦ rq }}) ∧
  (∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (rpc : RPC) (p : Loc) (rq : RequestPreVoteRequest),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     ⌜rpc.Command' = interface.mkOk (go.GoType.PointerType RequestPreVoteRequest.ty) #p ∧
       rq.RPCHeader'.ProtocolVersion' = W64 3⌝ ∗ p ↦ rq }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"checkRPCHeader")) (Val #rpc))
  {{ RET #interface.nil; p ↦ rq }}) ∧
  (∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (rpc : RPC) (p : Loc) (rq : TimeoutNowRequest),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     ⌜rpc.Command' = interface.mkOk (go.GoType.PointerType TimeoutNowRequest.ty) #p ∧
       rq.RPCHeader'.ProtocolVersion' = W64 3⌝ ∗ p ↦ rq }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"checkRPCHeader")) (Val #rpc))
  {{ RET #interface.nil; p ↦ rq }}) ∧
  (∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (rpc : RPC) (p : Loc) (rq : InstallSnapshotRequest),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     ⌜rpc.Command' = interface.mkOk (go.GoType.PointerType InstallSnapshotRequest.ty) #p ∧
       rq.RPCHeader'.ProtocolVersion' = W64 3⌝ ∗ p ↦ rq }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"checkRPCHeader")) (Val #rpc))
  {{ RET #interface.nil; p ↦ rq }})

end spec

end Perennial
