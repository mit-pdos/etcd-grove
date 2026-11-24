/-
The proof of `KvNet/Spec/.../kvnet/startNodeUDP.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`), at
the store's seam as `StartNode.wp_proof` (`kvFacts γ`, `kvRep γ vs dir`, `kvConfRead`, `kvStp γ vs dir`,
the start resource `kvNodeStart γ vs dir`): `openUDP`, then `startNode` with `u.newTransport` as the
constructor. `udpNet.newTransport.spec` gives `ptCtor` at any per-address premise, so at TCP's `tcpAP`,
where the kvnet lead's `start.spec` instance (`start.wp_proof`, at `tcpAP`, `kvStp`, `kvNodeStart`) is: the
UDP side reuses `start`, `stopIncarnation`, `kv_stepLaw` and `kv_confLaw` unchanged (as `StartNode`'s
proof uses them).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.startNodeUDP
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.openUDP
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__newTransport
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.startNode
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.start
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.stopIncarnation
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.StartDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ConfLaw
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.SendLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]
variable [go.IntoValInj GoString] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem startNodeUDP.wp_proof (γ : KdNames) (vs : List w64) (dir : GoString)
    (wp_openUDP : openUDP.spec (GF := GF) (hG := hG))
    (wp_newTransport : udpNet.newTransport.spec (GF := GF) (hG := hG))
    (wp_startNode : startNode.spec (GF := GF) (hG := hG) (kvFacts γ (fun _ => True)) (kvRep γ vs dir)
      (kvStp γ vs dir))
    (wp_start : start.spec (GF := GF) (hG := hG) (kvFacts γ (fun _ => True))
      (tcpAP (kvFacts γ (fun _ => True))) (kvRep γ vs dir) (kvStp γ vs dir) (kvNodeStart γ vs dir)
      γ.r.cluster kdRaftN)
    (wp_stopIncarnation : stopIncarnation.spec (GF := GF) (hG := hG) (kvStp γ vs dir)
      (kvNodeStart γ vs dir)) :
    startNodeUDP.spec (GF := GF) (hG := hG) (kvFacts γ (fun _ => True)) (kvRep γ vs dir) kvConfRead
      (kvStp γ vs dir) (kvNodeStart γ vs dir) := by
  sorry

end proof

end raft_kvnet
end EtcdGrove
end Perennial
