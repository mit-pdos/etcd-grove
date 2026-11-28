/-
`rpctransport.toPreVoteResp`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `toPreVoteResp(a)`: the wire message of `a`, with fresh byte slices. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.toPreVoteResp.spec : Prop :=
  ∀ (a : Loc) (dq : DFrac) (rq : github_com.hashicorp.raft.RequestPreVoteResponse) (dq1 : DFrac) (id ad  : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        a ↦{dq} rq ∗ rq.RPCHeader'.ID' ↦*{dq1} id ∗ rq.RPCHeader'.Addr' ↦*{dq1} ad }}
      (App (Val (@! toPreVoteResp)) (Val #a))
    {{ (i d  : GoSlice), RET #(PreVoteResp.mk false [] (Header.mk rq.RPCHeader'.ProtocolVersion' i d) rq.Term' rq.Granted'); a ↦{dq} rq ∗ rq.RPCHeader'.ID' ↦*{dq1} id ∗ rq.RPCHeader'.Addr' ↦*{dq1} ad ∗
        i ↦* id ∗ d ↦* ad }}

end spec

end Perennial
