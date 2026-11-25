/-
`startNodeUDP(cfg)` (`nodeudp.go`): `StartNode` with the UDP transport: the endpoint opened
(`openUDP`, from the process's UDP start `udpProcStart`), then the node started (`startNode`) with
`u.newTransport` as the constructor (`ptCtor` at any `AP`: `udpNet.newTransport`'s spec). At the
store's seams, as `StartNode.spec`: `S` the start resource, `rep`, `cf`, `stp`.
(kvudp, 2026-11-24: `notes/kvudp-proof-plan.md`.)
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.UdpBootDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeDefs

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
variable [go.IntoValInj GoString]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

/-- See the file header. -/
abbrev startNodeUDP.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF) (stp : NodeStopper GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options → GMap w64 GoString → IProp GF) : Prop :=
  ∀ (γu : UdpNames) (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeConfig) (M : GMap w64 GoString) (a : GoString),
  M !! cfg.ID' = some a →
  (∀ pid a', M !! pid = some a' → addrOk a' = true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ cfg.Addrs' ↦$□ M ∗ S cfg.ID' cfg.Dir' cfg.Opts' M ∗
      udpProcStart F γu cfg.ID' cfg.Dir' M }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.startNodeUDP)) (Val #cfg))
  {{ (nd u : Loc), RET (PairV #nd #u); ∃ (γ : Cluster) (N : Namespace) (boot : w64),
      isNodeS F rep stp nd γ N cfg.ID' ∗ confLaw F rep cf γ N cfg.ID' ∗
      isUdpNet F γu u cfg.ID' boot }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
