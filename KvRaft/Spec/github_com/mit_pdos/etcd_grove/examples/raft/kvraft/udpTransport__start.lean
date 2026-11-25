/-
`t.start(node)` (`udptransport.go`): the node set (read-only from now on) and a sender started
per peer (`runPeer`): the transport is started (`isUdpCore`).
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
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

/-- See the file header. -/
abbrev udpTransport.start.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : NodeH)
    (sc : Loc) (γsc : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ isUdpBase F γu t id sc γsc ∗
      (∃ v : GoInterface, t.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpTransport, go!"node"] ↦ v) ∗
      isNode n γ N id ∗ ⌜Cluster.trace γ = none⌝ }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpTransport.ty @!! go!"start")) (Val #(interface.mkOk (go.GoType.PointerType node.ty) #n.loc)))
  {{ RET #(); isUdpCore F γu t γ N id n }}

end spec

end kvraft
end EtcdGrove
end Perennial
