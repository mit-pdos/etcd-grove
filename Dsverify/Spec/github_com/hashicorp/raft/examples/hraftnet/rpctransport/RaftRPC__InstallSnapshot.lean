/-
`rpctransport.RaftRPC.InstallSnapshot`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Trans

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

/-- `s.InstallSnapshot(args, reply)`: as `AppendEntries`, the snapshot's bytes handed to raft in a reader over them. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.InstallSnapshot.spec : Prop :=
  ∀ (s : Loc) (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF) (i : github_com.hashicorp.raft.proto.SID) (W : net.rpc.RpcWorld GF)
    (C : net.rpc.CodecSpec GF) (args reply : Loc) (w : SnapReq) (v : SnapReqV) (snd : github_com.hashicorp.raft.proto.SID) (T s0 st : Nat),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ isRcv s γ snapP i W C ∗ args ↦ w ∗ snapReqOwn w (DFrac.own 1) v ∗ isReqW γ snapP v snd i T s0 st ∗
        reply ↦ (zeroValDef : SnapResp) }}
      (App (App (Val (s @!! go.GoType.PointerType RaftRPC.ty @!! go!"InstallSnapshot")) (Val #args)) (Val #reply))
    {{ RET #interface.nil; ∃ (w' : SnapResp) (r : SnapRespV), reply ↦ w' ∗ snapRespOwn w' (DFrac.own 1) r ∗ isRespW γ r }}

end spec

end Perennial
