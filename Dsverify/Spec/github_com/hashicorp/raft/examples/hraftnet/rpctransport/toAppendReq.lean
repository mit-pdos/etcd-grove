/-
`rpctransport.toAppendReq`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `toAppendReq(a)`: the wire request of raft's `a`, with fresh byte slices and entries. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.toAppendReq.spec : Prop :=
  ∀ (a : Loc) (dq : DFrac) (rq : github_com.hashicorp.raft.AppendEntriesRequest) (dq1 : DFrac)
    (id ad ld : List w8) (vs : List EntV),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        a ↦{dq} rq ∗ rq.RPCHeader'.ID' ↦*{dq1} id ∗ rq.RPCHeader'.Addr' ↦*{dq1} ad ∗
        rq.Leader' ↦*{dq1} ld ∗ logsOwn rq.Entries' dq1 vs }}
      (App (Val (@! toAppendReq)) (Val #a))
    {{ (p : Loc), RET #p; a ↦{dq} rq ∗ rq.RPCHeader'.ID' ↦*{dq1} id ∗ rq.RPCHeader'.Addr' ↦*{dq1} ad ∗
        rq.Leader' ↦*{dq1} ld ∗ logsOwn rq.Entries' dq1 vs ∗
        ∃ i d c es : GoSlice, p ↦ AppendReq.mk (Header.mk rq.RPCHeader'.ProtocolVersion' i d) rq.Term' c
          rq.PrevLogEntry' rq.PrevLogTerm' es rq.LeaderCommitIndex' ∗ i ↦* id ∗ d ↦* ad ∗ c ↦* ld ∗
          entsOwn es (DFrac.own 1) vs }}

end spec

end Perennial
