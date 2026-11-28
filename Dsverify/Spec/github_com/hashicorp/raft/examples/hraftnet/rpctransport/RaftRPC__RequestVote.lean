/-
`rpctransport.RaftRPC.RequestVote`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `s.RequestVote(args, reply)`: as `AppendEntries`, for a vote request. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.RequestVote.spec : Prop :=
  ∀ (s : Loc) (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF) (i : github_com.hashicorp.raft.proto.SID) (W : net.rpc.RpcWorld GF)
    (C : net.rpc.CodecSpec GF) (args reply : Loc) (w : VoteReq) (v : VoteReqV) (c : github_com.hashicorp.raft.proto.SID) (T li lt : Nat),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ isRcv s γ snapP i W C ∗ args ↦ w ∗ voteReqOwn w (DFrac.own 1) v ∗ rvReqW γ v c T li lt ∗
        reply ↦ (zeroValDef : VoteResp) }}
      (App (App (Val (s @!! go.GoType.PointerType RaftRPC.ty @!! go!"RequestVote")) (Val #args)) (Val #reply))
    {{ RET #interface.nil; ∃ (w' : VoteResp) (r : VoteRespV), reply ↦ w' ∗ voteRespOwn w' (DFrac.own 1) r ∗ rvRespW γ r i c T }}

end spec

end Perennial
