/-
The proof of `KvNet/Spec/.../kvnet/newReassembler.lean` (kvudp, phase 2: `notes/kvudp-proof-plan.md`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.newReassembler

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

theorem newReassembler.wp_proof :
    newReassembler.spec (GF := GF) (hG := hG) := by
  intro F γu sts
  wp_start as #Hs
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoSlice)) as %pm Hpm
  wp_apply (wp_map_make1 (K := w64) (V := GoSlice)) as %dm Hdm
  iapply wp_fupd
  wp_apply (wp_map_make1 (K := w64)
    (V := github_com.mit_pdos.etcd_grove.examples.raft.kvnet.msgID)) as %lm Hlm
  try wp_auto
  iStructNamed «$r0»
  ipersist pending
  ipersist done
  ipersist last
  ipersist stats
  imodintro
  iapply HΦ
  iunfold ownReassembler
  iexists pm, dm, lm, sts, ∅, ∅, ∅
  iframe pending done last stats Hs Hpm Hdm Hlm
  isplitl []
  · iapply BigSepM.bigSepM_empty.2; itrivial
  iapply BigSepM.bigSepM_empty.2; itrivial

end proof

end raft_kvnet
end EtcdGrove
end Perennial
