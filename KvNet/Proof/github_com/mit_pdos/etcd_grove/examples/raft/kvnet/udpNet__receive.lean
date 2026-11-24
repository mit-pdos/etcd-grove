/-
The proof of `KvNet/Spec/.../kvnet/udpNet__receive.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__receive
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.newReassembler
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__handle
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__stepper
public import KvNet.Spec.net.UDPConn__ReadFromUDP

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

theorem udpNet.receive.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF)
    (wp_newReassembler : newReassembler.spec (GF := GF) (hG := hG))
    (wp_stepper : udpNet.stepper.spec (GF := GF) (hG := hG) F rep stp)
    (wp_handle : udpNet.handle.spec (GF := GF) (hG := hG))
    (wp_ReadFromUDP : net.UDPConn.ReadFromUDP.spec (GF := GF) (hG := hG)) :
    udpNet.receive.spec (GF := GF) (hG := hG) F rep stp := by
  sorry

end proof

end raft_kvnet
end EtcdGrove
end Perennial
