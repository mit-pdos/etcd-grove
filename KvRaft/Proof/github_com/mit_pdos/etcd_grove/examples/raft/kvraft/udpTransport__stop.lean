/-
The proof of `KvRaft/Spec/.../kvraft/udpTransport__stop.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpTransport__stop

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
variable [net_sem : net.Assumptions]

theorem udpTransport.stop.wp_proof :
    udpTransport.stop.spec (GF := GF) (hG := hG) := by
  intro t sc γsc
  wp_start as ⟨#Hstopc, Hpend⟩
  iunfold transportStopper at Hpend
  ihave #Htt : □ (True : IProp GF) $$ []
  · imodintro; itrivial
  try wp_auto
  wp_apply wp_broadcast_chan_close sc γsc iprop(True) $$ [$Hpend $Htt] as -
  try wp_auto
  iapply HΦ
  itrivial

end proof

end kvraft
end EtcdGrove
end Perennial
