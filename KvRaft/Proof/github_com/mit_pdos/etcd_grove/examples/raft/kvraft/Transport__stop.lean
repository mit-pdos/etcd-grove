/-
The proof of `KvRaft/Spec/.../kvraft/Transport__stop.lean` (2026-11-24, G5): close the stop channel
(the broadcast's close, with its closer).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport__stop

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem Transport.stop.wp_proof : Transport.stop.spec (GF := GF) (hG := hG) := by
  intro t sc γsc
  wp_start as ⟨#Hts, Hpend⟩
  iunfold isTransportStop at Hts
  icases Hts with ⟨#Hstopc, #HstopB⟩
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
