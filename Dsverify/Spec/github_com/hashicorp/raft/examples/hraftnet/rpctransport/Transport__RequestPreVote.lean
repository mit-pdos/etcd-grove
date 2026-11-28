/-
`rpctransport.Transport.RequestPreVote`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `t.RequestPreVote(id, j, args, resp)`: as `AppendEntries`, for a pre-vote request. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.RequestPreVote.spec : Prop :=
  ∀ (t : Loc) (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF) (i : github_com.hashicorp.raft.proto.SID) (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) (id : GoString) (j : github_com.hashicorp.raft.proto.SID) (args resp : Loc) (rq : github_com.hashicorp.raft.RequestPreVoteRequest) (rp0 : github_com.hashicorp.raft.RequestPreVoteResponse) (dq : DFrac)
    (c : github_com.hashicorp.raft.proto.SID) (T : Nat),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ isTrans t γ snapP i W C ∗ args ↦{dq} rq ∗ github_com.hashicorp.raft.pvReq rq c T ∗ resp ↦ rp0 }}
      (App (App (App (App (Val (t @!! go.GoType.PointerType Transport.ty @!! go!"RequestPreVote")) (Val #id)) (Val #(j : GoString))) (Val #args)) (Val #resp))
    {{ (err : GoInterface), RET #err; args ↦{dq} rq ∗
        ((⌜err = interface.nil⌝ ∗ ∃ rp : github_com.hashicorp.raft.RequestPreVoteResponse, resp ↦ rp ∗ github_com.hashicorp.raft.pvResp γ rp T) ∨
         (errStr err ∗ resp ↦ rp0)) }}

end spec

end Perennial
