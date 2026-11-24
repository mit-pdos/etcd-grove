/-
The proof of `KvNet/Spec/.../kvnet/udpNet__handle.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__handle
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats__add
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getDatagram
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getMsg
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.reassembler__add
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.reassembler__remember
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__ack
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__acked
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType

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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

theorem udpNet.handle.wp_proof
    (wp_getDatagram : getDatagram.spec (GF := GF) (hG := hG))
    (wp_acked : udpNet.acked.spec (GF := GF) (hG := hG))
    (wp_add : reassembler.add.spec (GF := GF) (hG := hG))
    (wp_remember : reassembler.remember.spec (GF := GF) (hG := hG))
    (wp_ack : udpNet.ack.spec (GF := GF) (hG := hG))
    (wp_getMsg : getMsg.spec (GF := GF) (hG := hG))
    (wp_add_Stats : Stats.add.spec (GF := GF) (hG := hG))
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG)) :
    udpNet.handle.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end raft_kvnet
end EtcdGrove
end Perennial
