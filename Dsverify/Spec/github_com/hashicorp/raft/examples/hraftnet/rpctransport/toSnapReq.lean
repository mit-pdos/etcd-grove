/-
`rpctransport.toSnapReq`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `toSnapReq(a)`: the wire message of `a`, with fresh byte slices (and `data`, not copied). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.toSnapReq.spec : Prop :=
  ∀ (a : Loc) (dq : DFrac) (rq : github_com.hashicorp.raft.InstallSnapshotRequest) (dq1 : DFrac) (id ad b0 b1 b2 : List w8) (data : GoSlice),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        a ↦{dq} rq ∗ rq.RPCHeader'.ID' ↦*{dq1} id ∗ rq.RPCHeader'.Addr' ↦*{dq1} ad ∗
        rq.Leader' ↦*{dq1} b0 ∗
        rq.Peers' ↦*{dq1} b1 ∗
        rq.Configuration' ↦*{dq1} b2 }}
      (App (App (Val (@! toSnapReq)) (Val #a)) (Val #data))
    {{ (p : Loc), RET #p; a ↦{dq} rq ∗ rq.RPCHeader'.ID' ↦*{dq1} id ∗ rq.RPCHeader'.Addr' ↦*{dq1} ad ∗
        rq.Leader' ↦*{dq1} b0 ∗
        rq.Peers' ↦*{dq1} b1 ∗
        rq.Configuration' ↦*{dq1} b2 ∗
        ∃ i d c0 c1 c2 : GoSlice, p ↦ SnapReq.mk (Header.mk rq.RPCHeader'.ProtocolVersion' i d) rq.SnapshotVersion' rq.Term' c0 rq.LastLogIndex' rq.LastLogTerm' c1 c2 rq.ConfigurationIndex' rq.Size' data ∗ i ↦* id ∗ d ↦* ad ∗ c0 ↦* b0 ∗ c1 ↦* b1 ∗ c2 ↦* b2 }}

end spec

end Perennial
