/-
`rpctransport.Transport.RequestVote`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `t.RequestVote(id, j, args, resp)`: as `AppendEntries`, for a vote request. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.RequestVote.spec : Prop :=
  ∀ (t : Loc) (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF) (i : github_com.hashicorp.raft.proto.SID) (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) (id : GoString) (j : github_com.hashicorp.raft.proto.SID) (args resp : Loc) (rq : github_com.hashicorp.raft.RequestVoteRequest) (rp0 : github_com.hashicorp.raft.RequestVoteResponse) (dq : DFrac)
    (c : github_com.hashicorp.raft.proto.SID) (T li lt : Nat),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ isTrans t γ snapP i W C ∗ args ↦{dq} rq ∗ github_com.hashicorp.raft.rvReq γ rq c T li lt ∗ resp ↦ rp0 }}
      (App (App (App (App (Val (t @!! go.GoType.PointerType Transport.ty @!! go!"RequestVote")) (Val #id)) (Val #(j : GoString))) (Val #args)) (Val #resp))
    {{ (err : GoInterface), RET #err; args ↦{dq} rq ∗
        ((⌜err = interface.nil⌝ ∗ ∃ rp : github_com.hashicorp.raft.RequestVoteResponse, resp ↦ rp ∗ github_com.hashicorp.raft.rvResp γ rp j c T) ∨
         (errStr err ∗ resp ↦ rp0)) }}

end spec

end Perennial
