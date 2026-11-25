/-
The proof of `KvRaft/Spec/.../kvraft/BootFileOf.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.BootFileOf
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.itoa

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]
variable [go.IntoValInj GoString]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

theorem BootFileOf.wp_proof
    (wp_itoa : itoa.spec (GF := GF) (hG := hG)) :
    BootFileOf.spec (GF := GF) (hG := hG) := by
  intro dir id
  wp_start as #Hpkg
  wp_auto
  wp_apply wp_itoa id $$ [$Hpkg]
  unfold kvBootFileName
  iapply HΦ
  itrivial

end proof

end kvraft
end EtcdGrove
end Perennial
