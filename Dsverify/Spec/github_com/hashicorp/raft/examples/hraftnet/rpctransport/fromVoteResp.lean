/-
`rpctransport.fromVoteResp`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Wire

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

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

/-- `fromVoteResp(a)`: raft's message of `a`, with fresh byte slices. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromVoteResp.spec : Prop :=
  ∀ (a : Loc) (dq : DFrac) (rq : VoteResp) (dq1 : DFrac) (id ad b0 : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        a ↦{dq} rq ∗ rq.Hdr'.ID' ↦*{dq1} id ∗ rq.Hdr'.Addr' ↦*{dq1} ad ∗
        rq.Peers' ↦*{dq1} b0 }}
      (App (Val (@! fromVoteResp)) (Val #a))
    {{ (i d c0 : GoSlice), RET #(github_com.hashicorp.raft.RequestVoteResponse.mk (github_com.hashicorp.raft.RPCHeader.mk rq.Hdr'.ProtocolVersion' i d) rq.Term' c0 rq.Granted'); a ↦{dq} rq ∗ rq.Hdr'.ID' ↦*{dq1} id ∗ rq.Hdr'.Addr' ↦*{dq1} ad ∗
        rq.Peers' ↦*{dq1} b0 ∗
        i ↦* id ∗ d ↦* ad ∗ c0 ↦* b0 }}

end spec

end Perennial
