/-
`rpctransport.fromAppendReq`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `fromAppendReq(a)`: raft's request of the wire `a`, with fresh byte slices and log entries. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.fromAppendReq.spec : Prop :=
  ∀ (a : Loc) (dq : DFrac) (w : AppendReq) (dq1 : DFrac) (id ad ld : List w8) (vs : List EntV),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        a ↦{dq} w ∗ w.Hdr'.ID' ↦*{dq1} id ∗ w.Hdr'.Addr' ↦*{dq1} ad ∗
        w.Leader' ↦*{dq1} ld ∗ entsOwn w.Entries' dq1 vs }}
      (App (Val (@! fromAppendReq)) (Val #a))
    {{ (p : Loc), RET #p; a ↦{dq} w ∗ w.Hdr'.ID' ↦*{dq1} id ∗ w.Hdr'.Addr' ↦*{dq1} ad ∗
        w.Leader' ↦*{dq1} ld ∗ entsOwn w.Entries' dq1 vs ∗
        ∃ i d c es : GoSlice, p ↦ github_com.hashicorp.raft.AppendEntriesRequest.mk
            (github_com.hashicorp.raft.RPCHeader.mk w.Hdr'.ProtocolVersion' i d) w.Term' c
            w.PrevLogEntry' w.PrevLogTerm' es w.LeaderCommitIndex' ∗ i ↦* id ∗ d ↦* ad ∗ c ↦* ld ∗
          logsOwn es (DFrac.own 1) vs }}

end spec

end Perennial
