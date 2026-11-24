/-
`u.newTransport(id, addrs, stats)` (`udptransport.go`), the constructor `startNodeUDP` gives
`startNode`: a fresh transport of the peer-transport contract (`ptFresh`, `PeerTransport.lean`),
at any untraced cluster. Its peers are the endpoint's (`u.addrs`), not `addrs`, which it ignores:
so the function value meets `ptCtor` at **any** per-address premise `AP` (the endpoint holds what
the senders need of each address, from `openUDP`).
(kvudp, 2026-11-24: `notes/kvudp-proof-plan.md`.)
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.UdpDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.PeerTransport

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
abbrev udpNet.newTransport.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (u : Loc) (id boot : w64) (γ : Cluster) (N : Namespace) (am : Loc) (M : GMap w64 GoString) (sts : Loc),
  Cluster.trace γ = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ isUdpNet F γu u id boot ∗ am ↦$□ M ∗ isStats sts }}
    (App (App (App (Val (u @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet.ty @!! go!"newTransport")) (Val #id)) (Val #am)) (Val #sts))
  {{ (tv : GoInterface), RET #tv; ptFresh F γ N id tv }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
