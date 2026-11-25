/-
`RunUDP(cfg)` (`nodeudp.go`): `Run` with the raft messages over UDP: it listens for its clients
(TCP, `listen`, at the address's protocols), starts the node with the UDP transport
(`startNodeUDP`), starts the receiver (`udpNet.receive`) and accepts its clients (`Node.accept`).
At the store's seams, as `Run.spec`, and the process's UDP start. Never returns.
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
variable [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev RunUDP.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options → GMap w64 GoString → IProp GF) : Prop :=
  ∀ (γu : UdpNames) (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeConfig) (M : GMap w64 GoString)
    (a : GoString) (eof ed : GoInterface),
  M !! cfg.ID' = some a →
  (∀ pid a', M !! pid = some a' → addrOk a' = true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      cfg.Addrs' ↦$□ M ∗ addrProto a (kvP F cfg.ID') (kvQ F cfg.ID') ∗
      S cfg.ID' cfg.Dir' cfg.Opts' M ∗ udpProcStart F γu cfg.ID' cfg.Dir' M ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      context.isClosedchanInit }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.RunUDP)) (Val #cfg))
  {{ RET #(); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
