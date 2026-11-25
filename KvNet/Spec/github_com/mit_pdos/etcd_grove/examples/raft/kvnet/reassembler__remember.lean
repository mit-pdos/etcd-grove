/-
`r.remember(from, id, snap)` (`udptransport.go`): bookkeeping only (the completed names, the
stale messages in progress evicted).
(kvudp, 2026-11-24: `notes/kvudp-proof-plan.md`.)
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.UdpDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net Udp go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

/-- See the file header. -/
abbrev reassembler.remember.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (r : Loc) (src : w64) (mid : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.msgID) (snap : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ ownReassembler F γu r }}
    (App (App (App (Val (r @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.reassembler.ty @!! go!"remember")) (Val #src)) (Val #mid)) (Val #snap))
  {{ RET #(); ownReassembler F γu r }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
