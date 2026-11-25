/-
`t.dropped(m)` (`udptransport.go`): the node told that `m` was not sent (`ReportUnreachable`, and
`ReportSnapshot(SnapshotFailure)` for a snapshot: the untraced cluster `isUdpCore` has).
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
abbrev udpTransport.dropped.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : NodeH) (m : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ isUdpCore F γu t γ N id n ∗ msgPtsC m dq dqe cap st }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpTransport.ty @!! go!"dropped")) (Val #m))
  {{ RET #(); msgPtsC m dq dqe cap st }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
