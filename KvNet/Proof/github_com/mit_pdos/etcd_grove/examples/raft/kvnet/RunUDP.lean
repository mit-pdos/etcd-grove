/-
The proof of `KvNet/Spec/.../kvnet/RunUDP.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.RunUDP
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node__accept
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.listen
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.startNodeUDP
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.udpNet__receive

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
variable [go.IntoValInj GoString]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [field_sem : net.FieldAssumptions]

theorem RunUDP.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF) (stp : NodeStopper GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options → GMap w64 GoString → IProp GF)
    (wp_listen : listen.spec (GF := GF) (hG := hG))
    (wp_startNodeUDP : startNodeUDP.spec (GF := GF) (hG := hG) F rep cf stp S)
    (wp_receive : udpNet.receive.spec (GF := GF) (hG := hG) F rep stp)
    (wp_accept : Node.accept.spec (GF := GF) (hG := hG) F rep stp cf) :
    RunUDP.spec (GF := GF) (hG := hG) F rep cf S := by
  sorry

end proof

end raft_kvnet
end EtcdGrove
end Perennial
