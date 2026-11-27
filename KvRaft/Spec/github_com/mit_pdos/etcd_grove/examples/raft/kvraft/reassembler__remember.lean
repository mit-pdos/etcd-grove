/-
`r.remember(from, id, snap)` (`udptransport.go`): bookkeeping only (the completed names, the
stale messages in progress evicted).
(kvraft-udp, 2026-11-24: `notes/kvraft-udp-proof-plan.md`.)
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.UdpDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net Udp go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions]

/-- See the file header. -/
abbrev reassembler.remember.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (r : Loc) (src : w64) (mid : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.msgID) (snap : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ ownReassembler F γu r }}
    (App (App (App (Val (r @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.reassembler.ty @!! go!"remember")) (Val #src)) (Val #mid)) (Val #snap))
  {{ RET #(); ownReassembler F γu r }}

end spec

end kvraft
end EtcdGrove
end Perennial
