/-
`rpctransport.isHeartbeat`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `isHeartbeat(a)`: true only of a request with no previous entry, no entries and no commit index. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.isHeartbeat.spec : Prop :=
  ∀ (a : Loc) (dq : DFrac) (rq : github_com.hashicorp.raft.AppendEntriesRequest) (dq1 : DFrac) (ad ld : List w8) (ptrs : List Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ a ↦{dq} rq ∗ rq.RPCHeader'.Addr' ↦*{dq1} ad ∗ rq.Leader' ↦*{dq1} ld ∗ rq.Entries' ↦*{dq1} ptrs }}
      (App (Val (@! isHeartbeat)) (Val #a))
    {{ (b : Bool), RET #b; a ↦{dq} rq ∗ rq.RPCHeader'.Addr' ↦*{dq1} ad ∗ rq.Leader' ↦*{dq1} ld ∗ rq.Entries' ↦*{dq1} ptrs ∗
        ⌜b = true → rq.PrevLogEntry' = W64 0 ∧ ptrs = [] ∧ rq.LeaderCommitIndex' = W64 0⌝ }}

end spec

end Perennial
