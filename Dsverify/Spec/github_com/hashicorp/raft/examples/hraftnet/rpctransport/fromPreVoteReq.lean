/-
`rpctransport.fromPreVoteReq`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `fromPreVoteReq(a)`: raft's message of `a`, with fresh byte slices. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromPreVoteReq.spec : Prop :=
  ∀ (a : Loc) (dq : DFrac) (rq : PreVoteReq) (dq1 : DFrac) (id ad  : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        a ↦{dq} rq ∗ rq.Hdr'.ID' ↦*{dq1} id ∗ rq.Hdr'.Addr' ↦*{dq1} ad }}
      (App (Val (@! fromPreVoteReq)) (Val #a))
    {{ (p : Loc), RET #p; a ↦{dq} rq ∗ rq.Hdr'.ID' ↦*{dq1} id ∗ rq.Hdr'.Addr' ↦*{dq1} ad ∗
        ∃ i d  : GoSlice, p ↦ github_com.hashicorp.raft.RequestPreVoteRequest.mk (github_com.hashicorp.raft.RPCHeader.mk rq.Hdr'.ProtocolVersion' i d) rq.Term' rq.LastLogIndex' rq.LastLogTerm' ∗ i ↦* id ∗ d ↦* ad }}

end spec

end Perennial
